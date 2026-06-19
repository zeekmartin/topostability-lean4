"""
DECISIVE scaling test: does B2' <= lam2 G hold at all scales?

B2'_LHS = sum_e (min(d_a,d_b)-1)(f_a-f_b)^2
lam2 G  = lam2 (sum_e (f_a+f_b)^2 - S^2/m),   S = sum_v d_v f_v, m=|E|.
(Only degrees + Fiedler needed -- no triangle counts -- so large n is feasible.)

TASK1 deg2+dense (vertex of degree 2 attached to dense G(n-1,q)) at growing n.
TASK2 lollipop, barbell, glued cliques at scale.
Fit gap(n)~c n^alpha, margin(n)=1-ratio ~ c n^beta.
Run: python conjecture_B_B2prime_scaling.py
"""
import numpy as np
import networkx as nx


def metrics(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes)
    d = A.sum(1)
    L = np.diag(d) - A
    ev, U = np.linalg.eigh(L)
    lam = ev[1]; f = U[:, 1]
    f = f / np.linalg.norm(f)
    m = G.number_of_edges()
    S = float(d @ f)
    diff2 = np.subtract.outer(f, f) ** 2
    sum2 = np.add.outer(f, f) ** 2
    mind = np.minimum.outer(d, d)
    B2 = 0.5 * float((A * (mind - 1) * diff2).sum())     # ordered /2 = unordered edge sum
    Gvar = 0.5 * float((A * sum2).sum()) - S ** 2 / m
    target = lam * Gvar
    return dict(n=n, m=m, lam=lam, B2=B2, G=Gvar, target=target,
                ratio=B2 / target if target > 0 else np.inf, gap=target - B2)


def deg2_dense(n, q=0.65, seed=0):
    # dense core on n-1 vertices + one degree-2 vertex (the bottleneck)
    core = nx.gnp_random_graph(n - 1, q, seed=seed)
    # ensure connected core
    if not nx.is_connected(core):
        core = nx.connected_watts_strogatz_graph(n - 1, max(2, int(q * (n - 1))), 0.3, seed=seed)
    G = nx.Graph(core)
    v0 = n - 1
    G.add_node(v0)
    G.add_edge(v0, 0)
    G.add_edge(v0, 1)
    return G


def report(name, G):
    q = metrics(G)
    print(f"  {name:18s} n={q['n']:5d} m={q['m']:8d} lam2={q['lam']:.5f} "
          f"B2'={q['B2']:.4f} lam2G={q['target']:.4f} ratio={q['ratio']:.5f} "
          f"gap={q['gap']:.4f} margin={1-q['ratio']:.5f}")
    return q


def fit(ns, ys, label):
    ns = np.array(ns, float); ys = np.array(ys, float)
    mask = ys > 0
    if mask.sum() >= 2:
        a = np.polyfit(np.log(ns[mask]), np.log(ys[mask]), 1)
        print(f"    fit {label} ~ n^{a[0]:.3f}  (c={np.exp(a[1]):.3e})")
    else:
        print(f"    fit {label}: nonpositive values, cannot fit")


def main():
    print("=" * 80)
    print("TASK 1 — deg2+dense scaling (the critical test)")
    print("=" * 80)
    ns = [50, 100, 200, 500, 1000, 2000]
    qs = []
    for n in ns:
        qs.append(report(f"deg2dense n={n}", deg2_dense(n)))
    allpos = all(q['ratio'] < 1 for q in qs)
    print(f"  --> ratio < 1 at ALL sizes: {allpos}")
    fit(ns, [q['gap'] for q in qs], "gap")
    fit(ns, [q['lam'] for q in qs], "lam2")
    fit(ns, [q['G'] for q in qs], "G")
    fit(ns, [1 - q['ratio'] for q in qs], "margin")
    fit(ns, [q['gap'] / q['lam'] for q in qs], "gap/lam2")

    print("\n" + "=" * 80)
    print("TASK 2 — other hard families at scale")
    print("=" * 80)
    print(" lollipops K_m + path_L:")
    lps = []
    for m, Lp in ((10, 5), (20, 10), (50, 20), (100, 50)):
        lps.append(report(f"lollipop({m},{Lp})", nx.lollipop_graph(m, Lp)))
    print(" barbells K_m - path_L - K_m:")
    bbs = []
    for m, Lp in ((10, 5), (20, 10), (50, 20), (100, 50)):
        bbs.append(report(f"barbell({m},{Lp})", nx.barbell_graph(m, Lp)))
    print(" glued cliques K_m . K_m (share one vertex):")
    gls = []
    for m in (10, 20, 50, 100):
        # two K_m sharing a single vertex
        G = nx.complete_graph(m)
        H = nx.complete_graph(range(m - 1, 2 * m - 1))   # shares vertex m-1
        G.add_edges_from(H.edges())
        gls.append(report(f"glued K_{m}", G))

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    allfam = qs + lps + bbs + gls
    nfail = sum(1 for q in allfam if q['ratio'] >= 1 - 1e-12)
    worst = max(allfam, key=lambda q: q['ratio'])
    print(f"  total tested: {len(allfam)};  B2' >= lam2 G (failures): {nfail}")
    print(f"  worst ratio = {worst['ratio']:.5f} at n={worst['n']}  (margin {1-worst['ratio']:.5f})")
    if nfail == 0:
        print("  => B2' <= lam2 G holds at ALL tested scales: the conjecture is a degree-variance")
        print("     (triangle-free) inequality  Sum (min(d_a,d_b)-1)g^2 <= lam2(Sum h^2 - S^2/m).")
    else:
        print("  => B2' FAILS at scale; report crossover above.")


if __name__ == "__main__":
    main()
