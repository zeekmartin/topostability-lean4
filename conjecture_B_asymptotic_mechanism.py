"""
Asymptotic mechanism of  gap = lam2 G - B2'  on deg2+dense, as n -> infinity.

Two models:
  q=1  : deg-2 vertex v0 attached to a COMPLETE core K_{n-1}  (deterministic; analytically exact)
  q<1  : v0 attached to gnp(n-1, q)  (the user's random deg2+dense)

ANALYTIC (q=1, derived & verified): lam2 = 2 exactly; f_0=f_1=0 (Fiedler vanishes at attachments);
f_v0 = -sqrt((n-3)/(n-2)), f_bulk = 1/sqrt((n-3)(n-2)); B2' = Sum h^2 = 4(n-3)^2 z^2;
   gap = Sum h^2 - 2 S^2/m = 10(n-3)/m  > 0   (manifest: 2m-(n-4)^2 = 5(n-2) > 0),  gap ~ 20/n.

TASK1 leading terms & corrections (both models).
TASK2 which sub-terms of R''+C cancel.
TASK3 manifest positivity (q=1 closed form).
TASK4 does the mechanism generalize?
TASK5 the eigenvalue correction eps1 = 2 - lam2.
Run: python conjecture_B_asymptotic_mechanism.py
"""
import numpy as np
import networkx as nx
from conjecture_B_B2prime_scaling import deg2_dense


def deg2_complete(n):
    G = nx.complete_graph(n - 1); G.add_node(n - 1); G.add_edge(n - 1, 0); G.add_edge(n - 1, 1)
    return G


def analyze(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1)
    L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    v0 = int(np.argmin(d))                       # the degree-2 bottleneck vertex
    nb = list(np.where(A[v0] > 0)[0])
    # edge-type split
    es = [(idx[a], idx[b]) for a, b in G.edges()]
    B2 = Gsum = 0.0; B2_bott = B2_dense = 0.0; Gh_bott = Gh_dense = 0.0; T = 0.0
    A2 = A @ A
    for a, b in es:
        g = (f[a] - f[b]) ** 2; h = (f[a] + f[b]) ** 2
        w = min(d[a], d[b]) - 1
        B2 += w * g; Gsum += h; T += A2[a, b] * g
        if a == v0 or b == v0:
            B2_bott += w * g; Gh_bott += h
        else:
            B2_dense += w * g; Gh_dense += h
    Gvar = Gsum - S ** 2 / m
    gap = lam * Gvar - B2
    return dict(n=n, m=m, lam=lam, eps1=2 - lam, fv0=float(f[v0]),
                fnb=[float(f[x]) for x in nb], S=S, fDf=fDf, B2=B2, Gsum=Gsum, Gvar=Gvar,
                gap=gap, B2_bott=B2_bott, B2_dense=B2_dense, Gh_bott=Gh_bott, Gh_dense=Gh_dense,
                T=T, Spm=S ** 2 / m, dmax=float(d.max()))


def fit(ns, ys, lab):
    ns = np.array(ns, float); ys = np.array(ys, float)
    if np.all(np.abs(ys) > 1e-14):
        a = np.polyfit(np.log(ns), np.log(np.abs(ys)), 1)
        print(f"      {lab:16s} ~ n^{a[0]:+.3f}  (c={np.exp(a[1]):.3e})")


def main():
    print("=" * 78)
    print("PART A — q=1 (complete core): exact closed form")
    print("=" * 78)
    print(f"  {'n':>5} {'lam2':>9} {'gap':>10} {'10(n-3)/m':>11} {'Σh²-2S²/m':>11} {'B2''=Σh²?':>9}")
    for n in [50, 100, 200, 500, 1000]:
        q = analyze(deg2_complete(n))
        print(f"  {n:5d} {q['lam']:9.6f} {q['gap']:10.6f} {10*(n-3)/q['m']:11.6f} "
              f"{q['Gsum']-2*q['Spm']:11.6f} {abs(q['B2']-q['Gsum'])<1e-9}")
    print("  => lam2=2 EXACT; gap = Σh² - 2S²/m = 10(n-3)/m > 0; manifest: 2m-(n-4)²=5(n-2)>0.")
    print("     gap ~ 20/n.  f_0=f_1=0 (Fiedler vanishes at the two attachment vertices).")

    print("\n" + "=" * 78)
    print("PART B — random q=0.65: leading terms & corrections")
    print("=" * 78)
    ns = [50, 100, 200, 500, 1000, 2000]
    rows = [analyze(deg2_dense(n)) for n in ns]
    print(f"  {'n':>5} {'lam2':>8} {'eps1':>9} {'fv0':>7} {'gap':>9} {'B2_bott':>9} {'B2_dense':>9} "
          f"{'Gh_bott':>9} {'Gh_dense':>9} {'S²/m':>8}")
    for n, q in zip(ns, rows):
        print(f"  {n:5d} {q['lam']:8.5f} {q['eps1']:9.5f} {q['fv0']:7.3f} {q['gap']:9.5f} "
              f"{q['B2_bott']:9.4f} {q['B2_dense']:9.4f} {q['Gh_bott']:9.4f} {q['Gh_dense']:9.4f} "
              f"{q['Spm']:8.4f}")
    print("    fits:")
    fit(ns, [q['gap'] for q in rows], "gap")
    fit(ns, [q['eps1'] for q in rows], "eps1=2-lam2")
    fit(ns, [q['B2_bott'] for q in rows], "B2_bottleneck")
    fit(ns, [q['B2_dense'] for q in rows], "B2_dense")
    fit(ns, [q['Gh_bott'] for q in rows], "Σh²_bottleneck")
    fit(ns, [q['Gh_dense'] for q in rows], "Σh²_dense")
    fit(ns, [q['Spm'] for q in rows], "S²/m")
    fit(ns, [1 - q['fv0'] ** 2 for q in rows], "1-fv0²")

    print("\n" + "=" * 78)
    print("TASK 3/4 — manifest form gap = Σh² - 2S²/m ?  (exact for q=1; deviation otherwise)")
    print("=" * 78)
    print("  family            n     gap     Σh²-2S²/m   match?   (Σh²-2S²/m exact only if lam2=2 & B2'=Σh²)")
    tests = [("deg2+K(q=1)", deg2_complete(200)), ("deg2+dense q=.65", deg2_dense(200)),
             ("lollipop(100,50)", nx.lollipop_graph(100, 50)),
             ("barbell(50,20)", nx.barbell_graph(50, 20))]
    for name, G in tests:
        q = analyze(G)
        pred = q['Gsum'] - 2 * q['Spm']
        print(f"  {name:18s} {q['n']:5d} {q['gap']:8.4f} {pred:11.4f}   "
              f"{'YES' if abs(q['gap']-pred)<1e-6 else 'no (lam2=%.3f, B2-Σh²=%.2f)'%(q['lam'],q['B2']-q['Gsum'])}")

    print("\n" + "=" * 78)
    print("TASK 5 — eigenvalue correction eps1 = 2 - lam2")
    print("=" * 78)
    print("  q=1: eps1 = 0 EXACTLY (lam2=2).  random q=0.65: eps1 = 2-lam2 > 0, scaling:")
    fit(ns, [q['eps1'] for q in rows], "eps1 (random)")
    print("  eigenvector check (v0): (2-lam2) f_v0 = f_a + f_b ?")
    for n, q in zip(ns[:3], rows[:3]):
        lhs = q['eps1'] * q['fv0']; rhs = sum(q['fnb'])
        print(f"    n={n}: (2-lam2)f_v0={lhs:.5f}  f_a+f_b={rhs:.5f}  match={abs(lhs-rhs)<1e-3}")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print("  q=1 deg2 model: EXACT manifestly-positive gap = Σh² - 2S²/m = 10(n-3)/m ~ 20/n.")
    print("  Positivity reduces to 2m >= (n-4)^2 (margin 5(n-2)>0): edge-count beats squared deg-gap.")
    print("  q<1/lollipop/barbell: closed form is family-specific (lam2!=2, B2'!=Σh²); universal")
    print("  object is the variance G=Σh²-S²/m and the controlled deficit S²/m. eps1=2-lam2: 0 at")
    print("  q=1, >0 from incompleteness for q<1.")


if __name__ == "__main__":
    main()
