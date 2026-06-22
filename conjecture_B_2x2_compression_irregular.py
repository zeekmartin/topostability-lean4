"""
2x2 compression route for lam+S^2/m<=d_eff+1.
B = compression of A onto span{f, 1/sqrt n} = [[d_eff-lam, S/sqrt n],[S/sqrt n, 2m/n]].
Target <=> B22(B11+1)>=2 B12^2 <=> det(B) >= B12^2 - B22.
Interlacing: mu2(A) >= mu_min(B). Test what interlacing gives & whether it implies target.
Also test alternative compressions: span{f, d_centered}, and direct bounds.
Run: python conjecture_B_2x2_compression_irregular.py
"""
import numpy as np
import networkx as nx


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); d_eff = float(d @ (f * f))
    aev = np.linalg.eigvalsh(A); mu2A = aev[-2]; muminA = aev[0]; mu1A = aev[-1]
    # B on span{f, 1/sqrt n}
    B11 = d_eff - lam; B12 = S / np.sqrt(n); B22 = 2 * m / n
    B = np.array([[B11, B12], [B12, B22]])
    bev = np.linalg.eigvalsh(B); mumaxB = bev[1]; muminB = bev[0]
    detB = B11 * B22 - B12 ** 2
    target = detB - (B12 ** 2 - B22)            # >=0  <=> lam+S^2/m<=d_eff+1
    # alt compression span{f, dc} dc = d - dbar (centered degree), then 1/||.||
    dbar = 2 * m / n; dc = d - dbar
    # orthogonalize dc against f and 1 (project off span{f,1})
    dc2 = dc - (dc @ f) * f - (dc @ np.ones(n) / n) * np.ones(n)
    altmin = None
    if np.linalg.norm(dc2) > 1e-9:
        u = dc2 / np.linalg.norm(dc2)
        C = np.array([[f @ A @ f, f @ A @ u], [u @ A @ f, u @ A @ u]])
        altmin = float(np.linalg.eigvalsh(C)[0])
    return dict(n=n, lam=lam, S=S, m=m, d_eff=d_eff, mu2A=mu2A, muminA=muminA, mu1A=mu1A,
                B11=B11, B12=B12, B22=B22, muminB=muminB, mumaxB=mumaxB, detB=detB,
                target=target, S2m=S ** 2 / m, altmin=altmin)


def corpus():
    out = []; rng = np.random.default_rng(0)
    def deg2dense(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
        H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    def star(kc, ks):
        G = nx.complete_graph(kc)
        for i in range(ks): G.add_edge(0, kc + i)
        return G
    for nn in [30, 50, 80]:
        for q in [0.4, 0.6, 0.8, 0.9]: out.append((f"deg2d{nn}_{q}", deg2dense(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", nx.lollipop_graph(k, l)))
    out.append(("barb8_8", nx.barbell_graph(8, 8)))
    for nn in [25, 40, 60]:
        for q in [0.3, 0.5, 0.7, 0.85]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [12, 20]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [30, 50]:
        for kd in [1, 4, 10]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kd: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G)] if q is not None]
    print(f"  {len(data)} graphs")

    print("\n" + "=" * 92)
    print("TASK 1 — interlacing μ₂(A) >= μ_min(B) (should hold); and μ_min(B) >= -1 ?")
    print("=" * 92)
    il = sum(1 for _, q in data if q['mu2A'] >= q['muminB'] - 1e-7)
    m1 = sum(1 for _, q in data if q['muminB'] >= -1 - 1e-7)
    print(f"  μ₂(A) >= μ_min(B) (interlacing): {il}/{len(data)}")
    print(f"  μ_min(B) >= -1 : {m1}/{len(data)}  (min μ_min(B) = {min(q['muminB'] for _,q in data):.4f})")

    print("\n" + "=" * 92)
    print("TASK 3 — does the target det(B) >= B12² - B22 hold? (= lam+S²/m<=d_eff+1)")
    print("=" * 92)
    tg = sum(1 for _, q in data if q['target'] >= -1e-7)
    mn = min(data, key=lambda x: x[1]['target'])
    print(f"  target holds: {tg}/{len(data)}; min = {mn[1]['target']:.5f} at {mn[0]}")

    print("\n" + "=" * 92)
    print("TASK 2/4 — what does interlacing GIVE vs what target NEEDS? missing piece")
    print("=" * 92)
    # interlacing gives mu_min(B) <= mu2(A). Does target follow from mu_min(B) >= -1?
    # if mu_min(B)>=-1 then B+I psd => det(B+I)>=0 => (B11+1)(B22+1)>=B12^2 (WEAKER than target)
    # target needs (B11+1)B22 >= 2 B12^2. Compare.
    print(f"  {'graph':12s} {'target(det-...)':>14} {'μ_min(B)':>9} {'det(B+I)':>10} {'B22':>7} {'2B12²/B22-(B11+1)':>18}")
    for nm, q in sorted(data, key=lambda x: x[1]['target'])[:12]:
        detBpI = (q['B11'] + 1) * (q['B22'] + 1) - q['B12'] ** 2
        need = 2 * q['B12'] ** 2 / q['B22'] - (q['B11'] + 1)  # <=0 is target
        print(f"  {nm:12s} {q['target']:14.5f} {q['muminB']:9.4f} {detBpI:10.4f} {q['B22']:7.3f} {need:18.5f}")
    # does mu_min(B)>=-1 alone imply target? check graphs where mu_min(B)>=-1 but target tight
    print("  (μ_min(B)>=-1 gives (B11+1)(B22+1)>=B12², WEAKER than target (B11+1)B22>=2B12²)")

    print("\n" + "=" * 92)
    print("TASK 4 — alternative compression span{f, d_centered}: μ_min(C) and does it help?")
    print("=" * 92)
    alts = [(nm, q) for nm, q in data if q['altmin'] is not None]
    am1 = sum(1 for _, q in alts if q['altmin'] >= -1 - 1e-7)
    print(f"  span{{f,d_c}} compression C: μ_min(C) >= -1 in {am1}/{len(alts)}; "
          f"min μ_min(C) = {min(q['altmin'] for _,q in alts):.4f}")

    print("\n" + "=" * 92)
    print("TASK 5 — hard families: target slack + interlacing detail")
    print("=" * 92)
    for nm in ["deg2d80_0.9", "twin80_2", "star12_8", "lolli15_12", "K30-10", "gnp40_0.85"]:
        q = dict(data).get(nm)
        if q is None: continue
        print(f"  {nm:12s} target={q['target']:.4f} μ₂(A)={q['mu2A']:.3f} μ_min(B)={q['muminB']:.3f} "
              f"μ_min(A)={q['muminA']:.3f} d_eff={q['d_eff']:.2f} λ={q['lam']:.3f} S²/m={q['S2m']:.3f}")

    print("\n" + "=" * 92)
    print("SUMMARY / TASK 6")
    print("=" * 92)
    print(f"  interlacing μ₂(A)>=μ_min(B): {il}/{len(data)}; μ_min(B)>=-1: {m1}/{len(data)}; "
          f"target: {tg}/{len(data)}")
    print(f"  span{{f,d_c}} μ_min(C)>=-1: {am1}/{len(alts)}")
    print("  => see whether any 2x2 compression's μ_min>=-1 CLEANLY implies the target.")


if __name__ == "__main__":
    main()
