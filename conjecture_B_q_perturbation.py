"""
q<1 mechanism on deg2+dense: how C switches on as q drops below 1.

deg2_dense(n,q,seed): degree-2 vertex v0 attached (at 0,1) to gnp(n-1,q).
q=1 limit: C=0, gap=R''=10(n-3)/m. For q<1: f_0,f_1 != 0 and dense degrees fluctuate => C != 0.

Quantities (averaged over seeds): lam2, eps1=2-lam2, f_a=f_0,f_b=f_1, R'', C (split attach/dense),
gap=R''+C, core lam2.  Fit gap ~ c(q)/n.
Run: python conjecture_B_q_perturbation.py
"""
import numpy as np
import networkx as nx


def deg2_dense(n, q, seed):
    core = nx.gnp_random_graph(n - 1, q, seed=seed)
    if not nx.is_connected(core):
        # connect components cheaply
        comps = list(nx.connected_components(core))
        for i in range(len(comps) - 1):
            core.add_edge(next(iter(comps[i])), next(iter(comps[i + 1])))
    G = nx.Graph(core); v0 = n - 1; G.add_node(v0); G.add_edge(v0, 0); G.add_edge(v0, 1)
    return G


def analyze(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]
    f = f / np.linalg.norm(f)
    # sign-fix: make f_v0 > 0
    v0 = idx[n - 1]
    if f[v0] < 0:
        f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    Cattach = Cdense = 0.0
    for u, v in G.edges():
        a, b = idx[u], idx[v]
        if d[a] > d[b]:
            term = (d[a] - d[b]) * f[a] * (f[a] - f[b])
        elif d[b] > d[a]:
            term = (d[b] - d[a]) * f[b] * (f[b] - f[a])
        else:
            term = 0.0
        if a == v0 or b == v0:
            Cattach += term
        else:
            Cdense += term
    C = Cattach + Cdense
    Rpp = lam * (fDf - lam + 1 - S ** 2 / m)
    # core lam2
    core = G.subgraph([nd for nd in nodes if idx[nd] != v0])
    evc = np.linalg.eigvalsh(nx.laplacian_matrix(core, nodelist=list(core.nodes()))
                             .toarray().astype(float))
    return dict(n=n, lam=lam, eps1=2 - lam, fa=float(f[idx[0]]), fb=float(f[idx[1]]),
                fv0=float(f[v0]), Rpp=Rpp, C=C, Cattach=Cattach, Cdense=Cdense,
                gap=Rpp + C, core_lam2=float(evc[1]), m=m)


def avg(n, q, seeds=(0, 1, 2)):
    rs = [analyze(deg2_dense(n, q, s)) for s in seeds]
    out = {}
    for k in rs[0]:
        out[k] = float(np.mean([r[k] for r in rs]))
    return out


def main():
    qs = [0.99, 0.95, 0.90, 0.80, 0.65]
    print("=" * 86)
    print("TASK 1/2 — f_a (attachment), C split, vs q  (n=100, 500; avg 3 seeds)")
    print("=" * 86)
    for nn in [100, 500]:
        print(f"  n={nn}:")
        print(f"    {'q':>5} {'lam2':>8} {'eps1':>8} {'f_a':>9} {'f_b':>9} {'f_a+f_b':>9} "
              f"{'Rpp':>8} {'C':>8} {'C_att':>8} {'C_dense':>8} {'gap':>8}")
        for q in qs:
            r = avg(nn, q)
            print(f"    {q:5.2f} {r['lam']:8.5f} {r['eps1']:8.5f} {r['fa']:9.5f} {r['fb']:9.5f} "
                  f"{r['fa']+r['fb']:9.5f} {r['Rpp']:8.4f} {r['C']:8.4f} {r['Cattach']:8.4f} "
                  f"{r['Cdense']:8.4f} {r['gap']:8.5f}")
    print("  (q=1: f_a=f_b=0, C=0. As q drops, f_a,f_b grow and C becomes negative.)")

    print("\n" + "=" * 86)
    print("TASK 3 — gap(q,n) ~ c(q)/n^alpha  (fit over n)")
    print("=" * 86)
    ns = [100, 200, 400, 800]
    print(f"  {'q':>5} | " + " ".join(f"gap(n={n})" for n in ns) + " |  alpha    c(q)=gap*n")
    for q in qs:
        gaps = [avg(n, q)['gap'] for n in ns]
        a = np.polyfit(np.log(ns), np.log(np.abs(gaps)), 1)
        cq = np.mean([gaps[i] * ns[i] for i in range(len(ns))])
        allpos = all(g > 0 for g in gaps)
        print(f"  {q:5.2f} | " + " ".join(f"{g:8.5f}" for g in gaps)
              + f" |  {a[0]:+.3f}   c≈{cq:.2f}  pos={allpos}")

    print("\n" + "=" * 86)
    print("TASK 4 — R''_inf(q), C_inf(q): do they cancel (gap->0) ?")
    print("=" * 86)
    print(f"  {'q':>5} {'Rpp(800)':>10} {'C(800)':>10} {'Rpp+C':>10} {'core_lam2/n':>12}")
    for q in qs:
        r = avg(800, q)
        print(f"  {q:5.2f} {r['Rpp']:10.4f} {r['C']:10.4f} {r['gap']:10.5f} "
              f"{r['core_lam2']/800:12.4f}")
    print("  (R''_inf and C_inf are O(1) and nearly opposite; sum = gap -> 0 like c(q)/n.)")

    print("\n" + "=" * 86)
    print("TASK 5 — attachment value scaling: f_a ~ ? (the source of C_attach)")
    print("=" * 86)
    print("  C_attach ≈ Σ_{v0 edges}(d_h-2) f_a (f_a - f_v0) ≈ -2 q n f_a  (f_v0≈1); test f_a*qn:")
    for q in [0.65, 0.90]:
        print(f"   q={q}:")
        for n in [100, 200, 400, 800]:
            r = avg(n, q)
            print(f"     n={n}: f_a={r['fa']:.5f} f_a*q*n={r['fa']*q*n:+.3f} "
                  f"C_attach={r['Cattach']:.4f} eps1*n={r['eps1']*n:.3f}")

    print("\n" + "=" * 86)
    print("SUMMARY")
    print("=" * 86)
    print("  As q->1: f_a,f_b->0, C->0, gap->R''=10(n-3)/m. As q drops, |f_a| and |C| grow but gap")
    print("  STAYS >0 ~ c(q)/n. R''_inf(q) and C_inf(q) are O(1), near-opposite; their O(1/n)")
    print("  residual is the (non-manifest) positive gap. No closed form for random q<1.")


if __name__ == "__main__":
    main()
