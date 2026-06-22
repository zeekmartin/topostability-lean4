"""
Extend regular proof (gap>=lam(d+1-lam), via lam<=d+1) to irregular via effective-degree quantities.
gap=A-B-D. Regular: A-B = lam(n-lam)-C, C<=(n-1-d)lam, lam<=d+1 => gap>=lam(d+1-lam), D=0.

Effective degrees: d_eff=fDf, S=d.f, m_eff=Sum mdeg_v f_v^2 = (n-1)-d_eff (since ||f||=1).
Recall (complement signless): B = lam*Sum_ne h^2 = lam(2 m_eff - (n-lam)) = lam(2(n-1-d_eff)-(n-lam)).
Test candidate bounds: lam<=d_eff+1; lam+S^2/m<=d_eff+1; gap>=lam(d_eff+1-lam)-lam*S^2/m; etc.
Run: python conjecture_B_irregular_effective_degree.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]
    if ev[2] - lam < 1e-7: return None  # simple lam2 only
    f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); A2 = A @ A
    d_eff = float(d @ (f * f))                 # fDf
    d2 = float((d * d) @ (f * f))              # fD^2f
    d_var = d2 - d_eff ** 2
    m_eff = float(((n - 1) - d) @ (f * f))     # Sum mdeg_v f_v^2 = n-1-d_eff
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    nonedges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] == 0]
    Aterm = sum(sum(1 for c in range(n) if c != a and c != b and (A[a, c] == 0 or A[b, c] == 0))
                * (f[a] - f[b]) ** 2 for (a, b) in edges)
    Bterm = lam * sum((f[i] + f[j]) ** 2 for i, j in nonedges)
    Dterm = lam * S ** 2 / m
    gap = Aterm - Bterm - Dterm
    return dict(n=n, lam=lam, S=S, m=m, d_eff=d_eff, d_var=d_var, m_eff=m_eff,
                A=Aterm, B=Bterm, D=Dterm, gap=gap, S2m=S ** 2 / m,
                regular=(d.max() == d.min()), dmin=float(d.min()), dmax=float(d.max()))


def families():
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
        for q in [0.4, 0.6, 0.8]: out.append((f"deg2d{nn}_{q}", deg2dense(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for k, l in [(10, 10), (15, 12), (20, 8)]: out.append((f"lolli{k}_{l}", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8), (12, 6)]: out.append((f"barb{k}_{l}", nx.barbell_graph(k, l)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", star(kc, ks)))
    for nn in [25, 40, 60]:
        for q in [0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [30, 50]:
        for kdel in [1, 4]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kdel: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = [(nm, q) for nm, G in families() for q in [quant(G)] if q is not None]
    print(f"  {len(data)} simple-λ₂ graphs")

    print("\n" + "=" * 96)
    print("TASK 2 — candidate spectral bounds (all should hold if regular-template extends)")
    print("=" * 96)
    c1 = sum(1 for _, q in data if q['lam'] <= q['d_eff'] + 1 + 1e-9)
    c2 = sum(1 for _, q in data if q['lam'] + q['S2m'] <= q['d_eff'] + 1 + 1e-9)
    c3 = sum(1 for _, q in data if q['lam'] <= q['dmax'] + 1 + 1e-9)
    print(f"  λ ≤ d_eff+1            : {c1}/{len(data)}")
    print(f"  λ + S²/m ≤ d_eff+1     : {c2}/{len(data)}")
    print(f"  λ ≤ Δ+1 (max degree)   : {c3}/{len(data)}")

    print("\n" + "=" * 96)
    print("TASK 3 — candidate gap lower bounds: which hold? margin?")
    print("=" * 96)
    # LB1: lam(d_eff+1-lam)-lam*S2m ;  LB2: lam(d_eff+1-lam-S2m) (same);  LB3: with d_var correction
    print(f"  {'graph':12s} {'gap':>8} {'LB=λ(d_eff+1-λ)-λS²/m':>22} {'gap>=LB?':>9} {'d_var':>8} {'reg':>4}")
    lb_ok = 0
    for nm, q in sorted(data, key=lambda x: x[1]['gap'])[:16]:
        LB = q['lam'] * (q['d_eff'] + 1 - q['lam']) - q['lam'] * q['S2m']
        ok = q['gap'] >= LB - 1e-9
        print(f"  {nm:12s} {q['gap']:8.4f} {LB:22.4f} {str(ok):>9} {q['d_var']:8.4f} {str(q['regular']):>4}")
    lb_ok = sum(1 for _, q in data if q['gap'] >= q['lam'] * (q['d_eff'] + 1 - q['lam']) - q['lam'] * q['S2m'] - 1e-9)
    print(f"  gap >= λ(d_eff+1-λ) - λS²/m : {lb_ok}/{len(data)}")

    print("\n" + "=" * 96)
    print("TASK 3b — alternative: gap >= λ(d_eff+1-λ) - λS²/m - c·d_var ? find needed c")
    print("=" * 96)
    # if LB1 fails, see if subtracting d_var fixes it: needed c = max over fails of (LB1-gap)/d_var
    fails = [(nm, q) for nm, q in data if q['gap'] < q['lam'] * (q['d_eff'] + 1 - q['lam']) - q['lam'] * q['S2m'] - 1e-9]
    print(f"  LB1 failures: {len(fails)}")
    for nm, q in fails[:8]:
        LB1 = q['lam'] * (q['d_eff'] + 1 - q['lam']) - q['lam'] * q['S2m']
        need = (LB1 - q['gap']) / q['d_var'] if q['d_var'] > 1e-9 else float('inf')
        print(f"    {nm:12s} gap={q['gap']:.4f} LB1={LB1:.4f} deficit={LB1-q['gap']:.4f} d_var={q['d_var']:.4f} need c>={need:.3f}")

    print("\n" + "=" * 96)
    print("TASK 5 — sharp candidate: which LB is tight & equality family?")
    print("=" * 96)
    # check tightness gap-LB for the best-holding LB
    print(f"  {'graph':12s} {'gap':>8} {'λ(d_eff+1-λ)':>14} {'gap-that':>9} {'-λS²/m':>9}")
    for nm, q in sorted(data, key=lambda x: x[1]['gap'])[:8]:
        base = q['lam'] * (q['d_eff'] + 1 - q['lam'])
        print(f"  {nm:12s} {q['gap']:8.4f} {base:14.4f} {q['gap']-base:9.4f} {-q['lam']*q['S2m']:9.4f}")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  λ≤d_eff+1:{c1}/{len(data)} λ+S²/m≤d_eff+1:{c2}/{len(data)}; "
          f"gap>=λ(d_eff+1-λ)-λS²/m:{lb_ok}/{len(data)}")


if __name__ == "__main__":
    main()
