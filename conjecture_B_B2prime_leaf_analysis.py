"""
Sharpness of B2' <= 2*lam*degQuad (ordered Lean convention).
  B2'_ord = Sum_i Sum_j [Adj](min(d_i,d_j)-1)(f_i-f_j)^2   (= 2 * unordered)
  RHS     = 2*lam*degQuad = 2*lam*Sum d_v f_v^2  (||f||=1 => 2*lam*d_eff)
ratio = B2'_ord/RHS. Find extremizers; compare regimes; test weighted-degree reduction
  min(d_a,d_b)-1 <= alpha(d_a+d_b)  and  B2' <= alpha*W_ord <= 2*lam*degQuad.
Run: python conjecture_B_B2prime_leaf_analysis.py
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
    B2 = 2 * sum((min(d[a], d[b]) - 1) * g2[(a, b)] for a, b in edges)       # ordered
    W = 2 * sum((d[a] + d[b]) * g2[(a, b)] for a, b in edges)                 # ordered W
    RHS = 2 * lam * d_eff
    # per-edge alpha = (min-1)/(d_a+d_b); gradient-weighted alpha
    num = sum((min(d[a], d[b]) - 1) * g2[(a, b)] for a, b in edges)
    den = sum((d[a] + d[b]) * g2[(a, b)] for a, b in edges)
    alpha_w = num / den if den > 0 else 0.0
    alpha_max = max((min(d[a], d[b]) - 1) / (d[a] + d[b]) for a, b in edges)
    return dict(n=n, lam=lam, d_eff=d_eff, B2=B2, W=W, RHS=RHS,
                ratio=B2 / RHS if RHS > 0 else 0.0,
                W_over_RHS=W / RHS if RHS > 0 else 0.0,
                alpha_w=alpha_w, alpha_max=alpha_max, regular=(d.max() == d.min()))


def corpus():
    out = []; rng = np.random.default_rng(0)
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    for nn in [30, 50, 80]:
        for q in [0.3, 0.5, 0.7, 0.9]: out.append((f"deg2d{nn}_{q}", "TYPEA", d2(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", "TYPEA", twin(N, dd)))
    for k, l in [(10, 10), (15, 12), (20, 8)]: out.append((f"lolli{k}_{l}", "TYPEB", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8), (12, 6)]: out.append((f"barb{k}_{l}", "TYPEB", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", "RANDOM", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, 8, nn // 2]:
            if 3 <= r < nn and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", "REGULAR", nx.random_regular_graph(r, nn, seed=1)))
    for nn in [10, 15, 20, 30, 50]: out.append((f"K{nn}", "REGULAR", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, cl, q) for nm, cl, G in corpus() for q in [quant(G)] if q is not None]
    print(f"  {len(data)} graphs; B2' <= 2λ·degQuad holds: "
          f"{sum(1 for _,_,q in data if q['ratio']<=1+1e-7)}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 1/2 — ratio B2'/(2λ·degQuad); extremizers (ratio -> 1 = sharp)")
    print("=" * 92)
    print(f"  {'graph':12s} {'class':>8} {'ratio':>8} {'1-ratio':>9} {'n':>4}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['ratio'])[:16]:
        print(f"  {nm:12s} {cl:>8} {q['ratio']:8.4f} {1-q['ratio']:9.5f} {q['n']:4d}")

    print("\n" + "=" * 92)
    print("TASK 3/4 — ratio by class (mean / max); are hard cases TYPE A or other?")
    print("=" * 92)
    from collections import defaultdict
    by = defaultdict(list)
    for nm, cl, q in data: by[cl].append(q['ratio'])
    for cl, rs in sorted(by.items()):
        print(f"  {cl:8s}: n={len(rs):2d}  mean ratio={np.mean(rs):.4f}  MAX ratio={max(rs):.4f}")

    print("\n" + "=" * 92)
    print("Kn asymptotics (extremizer?): ratio -> 1 as n grows")
    print("=" * 92)
    for nm, cl, q in [(nm, cl, q) for nm, cl, q in data if nm.startswith("K")]:
        print(f"  {nm:6s} ratio={q['ratio']:.5f}  (pred (n-2)/(n-1)={(q['n']-2)/(q['n']-1):.5f})")

    print("\n" + "=" * 92)
    print("TASK 5 — weighted-degree reduction: min(d_a,d_b)-1 <= alpha(d_a+d_b)")
    print("=" * 92)
    print("  gradient-weighted alpha_w = B2'/W; per-edge alpha_max; and W/(2λ degQuad)")
    print(f"  {'graph':12s} {'class':>8} {'alpha_w':>8} {'alpha_max':>9} {'W/RHS':>8}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['ratio'])[:12]:
        print(f"  {nm:12s} {cl:>8} {q['alpha_w']:8.4f} {q['alpha_max']:9.4f} {q['W_over_RHS']:8.4f}")
    aw = [q['alpha_w'] for _, _, q in data]
    wr = [q['W_over_RHS'] for _, _, q in data]
    print(f"\n  alpha_w range [{min(aw):.4f}, {max(aw):.4f}]  (1/2 is the min<=avg ceiling)")
    print(f"  W/(2λ degQuad) range [{min(wr):.3f}, {max(wr):.3f}]")
    # chain test: B2' <= alpha*W <= 2λ degQuad needs alpha*W <= RHS i.e. alpha <= RHS/W
    print(f"  chain B2'<=(1/2)W<=2λdegQuad valid (i.e. W<=4λdegQuad)? "
          f"{sum(1 for _,_,q in data if q['W_over_RHS']<=2+1e-7)}/{len(data)} (need W/RHS<=2)")
    print(f"  alpha_w * (W/RHS) = ratio (consistency). Does a UNIFORM alpha give B2'<=2λdegQuad via W? "
          f"only if W/RHS bounded -> W route {'FAILS' if max(wr)>4 else 'maybe'} (max W/RHS={max(wr):.2f})")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    mx = max(data, key=lambda x: x[2]['ratio'])
    print(f"  sharpest: {mx[0]} ({mx[1]}) ratio={mx[2]['ratio']:.5f}")
    print(f"  TYPE A max ratio={max(by['TYPEA']):.4f}; REGULAR(incl Kn) max={max(by['REGULAR']):.4f}")


if __name__ == "__main__":
    main()
