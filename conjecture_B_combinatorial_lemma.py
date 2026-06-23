"""
Combinatorial lemma R>=0: T <= lam(d_eff - 1).  T=Sum_e t_e g^2, d_eff=fDf, lam=Sum_e g^2.
Proof attempt: t_e<=min(d_a,d_b)-1<=(d_a+d_b)/2-1 => T<=B2'<=W/2-lam (W=Sum(d_a+d_b)g^2).
Then suffices W<=2 lam d_eff. Test all routes + apex.
Run: python conjecture_B_combinatorial_lemma.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f)); A2 = A @ A
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    g2 = {(a, b): (f[a] - f[b]) ** 2 for (a, b) in edges}
    T = sum(A2[a, b] * g2[(a, b)] for (a, b) in edges)
    B2 = sum((min(d[a], d[b]) - 1) * g2[(a, b)] for (a, b) in edges)
    W = sum((d[a] + d[b]) * g2[(a, b)] for (a, b) in edges)
    lam_e = sum(g2.values())  # = lam (should match)
    return dict(n=n, lam=lam, d_eff=d_eff, T=T, B2=B2, W=W,
                target=lam * (d_eff - 1) - T,          # R>=0
                aggregate=lam * d_eff - T,             # T<=lam d_eff (weaker)
                W_route=2 * lam * d_eff - W,           # W<=2 lam d_eff ?
                B2_route=lam * (d_eff - 1) - B2,       # B2'<=lam(d_eff-1) ?
                W2ml_route=lam * (d_eff - 1) - (W / 2 - lam),  # W/2-lam<=lam(d_eff-1) <=> W<=2lam d_eff
                regular=(d.max() == d.min()))


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
    for nn in [30, 50, 80, 110]:
        for q in [0.3, 0.5, 0.7, 0.85, 0.95]: out.append((f"deg2d{nn}_{q}", deg2dense(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4, 6]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8), (15, 15)]: out.append((f"star{kc}_{ks}", star(kc, ks)))
    for k, l in [(10, 10), (15, 12), (20, 8)]: out.append((f"lolli{k}_{l}", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8), (12, 6)]: out.append((f"barb{k}_{l}", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.2, 0.35, 0.5, 0.7, 0.85]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, 8]:
            if (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", nx.random_regular_graph(r, nn, seed=1)))
    for nn in [12, 20, 30]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [30, 50]:
        for kd in [1, 5, 12]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kd: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [quant(G)] if q is not None]
    print(f"  {len(data)} graphs")

    print("\n" + "=" * 92)
    print("TASK 1 — R>=0 i.e. T<=λ(d_eff-1) on expanded corpus")
    print("=" * 92)
    ok = sum(1 for _, q in data if q['target'] >= -1e-7)
    mn = min(data, key=lambda x: x[1]['target'])
    print(f"  T<=λ(d_eff-1): {ok}/{len(data)}; min slack = {mn[1]['target']:.6f} at {mn[0]}")
    print(f"  (compare aggregate T<=λ d_eff: {sum(1 for _,q in data if q['aggregate']>=-1e-7)}/{len(data)})")

    print("\n" + "=" * 92)
    print("TASK 3/5 — proof routes. min slack of each (>=0 means route valid):")
    print("=" * 92)
    for key, desc in [("B2_route", "B2'<=λ(d_eff-1)  [T<=B2'<=this?]"),
                      ("W_route", "W<=2λ d_eff"),
                      ("W2ml_route", "W/2-λ<=λ(d_eff-1) (=W<=2λd_eff)")]:
        vals = [q[key] for _, q in data]
        ng = sum(1 for v in vals if v >= -1e-7)
        am = min(data, key=lambda x: x[1][key])
        print(f"  {desc:34s}: holds {ng}/{len(data)}; min = {min(vals):.4f} at {am[0]}")

    print("\n" + "=" * 92)
    print("TASK 5 — does T<=B2'<=W/2-λ<=λ(d_eff-1) chain hold? (per-edge route)")
    print("=" * 92)
    # T<=B2' always (per-edge); B2'<=W/2-λ always (min<=avg); need W/2-λ<=λ(d_eff-1) i.e W<=2λd_eff
    tb2 = sum(1 for _, q in data if q['T'] <= q['B2'] + 1e-9)
    b2w = sum(1 for _, q in data if q['B2'] <= q['W'] / 2 - q['lam'] + 1e-9)
    print(f"  T<=B2' (per-edge): {tb2}/{len(data)}")
    print(f"  B2'<=W/2-λ (min<=avg): {b2w}/{len(data)}")
    print(f"  W<=2λd_eff (the gap): {sum(1 for _,q in data if q['W_route']>=-1e-7)}/{len(data)}")
    print("  => if all three hold, T<=λ(d_eff-1) PROVEN via per-edge route (NO apex needed)")

    print("\n" + "=" * 92)
    print("TASK 4 — where W<=2λd_eff fails/tightest; is it the bottleneck?")
    print("=" * 92)
    for nm, q in sorted(data, key=lambda x: x[1]['W_route'])[:10]:
        print(f"  {nm:12s} W={q['W']:.3f} 2λd_eff={2*q['lam']*q['d_eff']:.3f} slack={q['W_route']:.4f} "
              f"target(R)={q['target']:.4f} {'REG' if q['regular'] else ''}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  T<=λ(d_eff-1): {ok}/{len(data)}; W<=2λd_eff: "
          f"{sum(1 for _,q in data if q['W_route']>=-1e-7)}/{len(data)}; "
          f"B2'<=λ(d_eff-1): {sum(1 for _,q in data if q['B2_route']>=-1e-7)}/{len(data)}")
    print("  => if W<=2λd_eff holds universally, per-edge route PROVES the combinatorial lemma.")


if __name__ == "__main__":
    main()
