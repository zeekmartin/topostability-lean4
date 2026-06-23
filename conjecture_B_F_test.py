"""
Test F = Sum_v (d_v-1) D_v  vs  2*lam*d_eff   (ordered Lean convention).
  D_v = Sum_{u~v}(f_v-f_u)^2 (ordered local Dirichlet);  F = Sum_v(d_v-1)D_v = Sum_e(d_a+d_b-2)g^2.
  B2'_ord = Sum_{i,j}[Adj](min(d_i,d_j)-1)(f_i-f_j)^2 = 2*Sum_e(min-1)g^2.
  Algebra: F - B2'_ord = Sum_e |d_a-d_b| g^2 (degree-imbalance energy) >= 0.
Question: does F <= 2*lam*d_eff hold? (B2'<=F is trivial; if F>2lam*d_eff the F route is DEAD.)
Run: python conjecture_B_F_test.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f))
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    g2 = {(a, b): (f[a] - f[b]) ** 2 for a, b in edges}
    F = sum((d[a] + d[b] - 2) * g2[(a, b)] for a, b in edges)                  # = Sum_v(d_v-1)D_v
    B2 = 2 * sum((min(d[a], d[b]) - 1) * g2[(a, b)] for a, b in edges)         # ordered
    imbal = sum(abs(d[a] - d[b]) * g2[(a, b)] for a, b in edges)              # F - B2
    RHS = 2 * lam * d_eff
    return dict(n=n, lam=lam, d_eff=d_eff, F=F, B2=B2, imbal=imbal, RHS=RHS,
                F_ratio=F / RHS if RHS > 0 else 0.0,
                B2_ratio=B2 / RHS if RHS > 0 else 0.0,
                regular=(d.max() == d.min()))


def corpus():
    out = []; rng = np.random.default_rng(0)
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
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
        for q in [0.3, 0.5, 0.7, 0.9]: out.append((f"deg2d{nn}_{q}", "TYPEA", d2(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", "TYPEA", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8), (15, 15)]: out.append((f"star{kc}_{ks}", "CLIQUESTAR", star(kc, ks)))
    for k, l in [(10, 10), (15, 12), (20, 8)]: out.append((f"lolli{k}_{l}", "TYPEB", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8), (12, 6)]: out.append((f"barb{k}_{l}", "TYPEB", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", "RANDOM", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, 8, nn // 2]:
            if 3 <= r < nn and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", "REGULAR", nx.random_regular_graph(r, nn, seed=1)))
    for nn in [10, 20, 30, 50]: out.append((f"K{nn}", "REGULAR", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, cl, q) for nm, cl, G in corpus() for q in [quant(G)] if q is not None]
    hold = sum(1 for _, _, q in data if q['F_ratio'] <= 1 + 1e-7)
    print(f"  {len(data)} graphs; F <= 2λ·d_eff holds: {hold}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 1/2 — F/(2λ·d_eff); >1 means ROUTE DEAD")
    print("=" * 92)
    viol = [(nm, cl, q) for nm, cl, q in data if q['F_ratio'] > 1 + 1e-7]
    print(f"  F > 2λ·d_eff (route-killing): {len(viol)}/{len(data)}")
    print(f"  {'graph':12s} {'class':>11} {'F_ratio':>8} {'B2_ratio':>9} {'cost(imbal/RHS)':>16}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['F_ratio'])[:18]:
        flag = "  <-- DEAD" if q['F_ratio'] > 1 + 1e-7 else ""
        print(f"  {nm:12s} {cl:>11} {q['F_ratio']:8.4f} {q['B2_ratio']:9.4f} {q['imbal']/q['RHS']:16.4f}{flag}")

    if viol:
        print("\n" + "=" * 92)
        print("TASK 2 — ROUTE DEAD. F exceeds 2λ·d_eff on:")
        print("=" * 92)
        from collections import Counter
        c = Counter(cl for _, cl, _ in viol)
        for k, v in c.items(): print(f"  {k}: {v} graphs")
        mx = max(viol, key=lambda x: x[2]['F_ratio'])
        print(f"  worst: {mx[0]} ({mx[1]}) F/RHS={mx[2]['F_ratio']:.4f}")
    else:
        print("\n  TASK 3 — F<=2λd_eff everywhere; extremizer:")
        mx = max(data, key=lambda x: x[2]['F_ratio'])
        print(f"  extremizer {mx[0]} ({mx[1]}) F/RHS={mx[2]['F_ratio']:.4f}")

    print("\n" + "=" * 92)
    print("TASK 4 — cost of the step B2' <= F  (= Σ|d_a-d_b|g² / RHS), by class")
    print("=" * 92)
    from collections import defaultdict
    by = defaultdict(list)
    for nm, cl, q in data: by[cl].append((q['B2_ratio'], q['F_ratio'], q['imbal'] / q['RHS']))
    print(f"  {'class':12s} {'B2_ratio(mean)':>14} {'F_ratio(mean)':>14} {'F_ratio(MAX)':>13} {'cost(max)':>10}")
    for cl, rs in sorted(by.items()):
        b = np.mean([x[0] for x in rs]); fr = np.mean([x[1] for x in rs])
        fmx = max(x[1] for x in rs); cmx = max(x[2] for x in rs)
        print(f"  {cl:12s} {b:14.4f} {fr:14.4f} {fmx:13.4f} {cmx:10.4f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  F<=2λd_eff: {hold}/{len(data)}. "
          f"{'ROUTE DEAD (F overshoots — B2 step too lossy on imbalance).' if viol else 'F route survives.'}")


if __name__ == "__main__":
    main()
