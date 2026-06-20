"""
Exact joint formula R'' + C_attach for the deg-2 TYPE A model, and the sub-leading residual.

x=f_v0, y=f_a+f_b, lam=lam2, d_a,d_b = G-degrees of attachments. Bottleneck: (2-lam)x = y.
C_attach = (d_a-2)f_a(f_a-x) + (d_b-2)f_b(f_b-x)             [exact, for d_a,d_b>2]
fDf = 2x^2 + d_a f_a^2 + d_b f_b^2 + sum_C d_u f_u^2          [exact split]
S   = 2x + d_a f_a + d_b f_b + sum_C d_u f_u                 [exact split]
R'' = lam(fDf - lam + 1 - S^2/m)

Leading: R''_inf = -C_attach_inf = 2(1-q)x^2 (cancel). Goal: isolate the positive sub-leading residual
and test forms: c*(2-lam), c*core_var, c*(f_a-f_b)^2, c/m*(deg expr).
Run: python conjecture_B_typeA_joint_cancellation.py
"""
import numpy as np
import networkx as nx
from conjecture_B_core_gap_stability import attach_deg2


def analyze(H):
    G, v0lbl = attach_deg2(H)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[v0lbl]
    if f[v0] < 0:
        f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    x = float(f[v0]); a, b = idx[0], idx[1]
    fa, fb = float(f[a]), float(f[b]); y = fa + fb
    da, db = float(d[a]), float(d[b])
    # exact C_attach and full C
    Catt = (da - 2) * fa * (fa - x) + (db - 2) * fb * (fb - x)
    Cfull = 0.0
    for u, v in G.edges():
        ia, ib = idx[u], idx[v]
        if d[ia] > d[ib]:
            Cfull += (d[ia] - d[ib]) * f[ia] * (f[ia] - f[ib])
        elif d[ib] > d[ia]:
            Cfull += (d[ib] - d[ia]) * f[ib] * (f[ib] - f[ia])
    Cdense = Cfull - Catt
    Rpp = lam * (fDf - lam + 1 - S ** 2 / m)
    gap = Rpp + Cfull
    # core stats
    coremask = np.array([idx[u] for u in range(v0lbl)])
    fcore = f[coremask]; dcore = d[coremask] - np.array([1 if u in (0, 1) else 0 for u in range(v0lbl)])
    mu = float(fcore.mean()); eta = fcore - mu
    core_var = float(eta @ eta)            # ||f_core_perp||^2
    Hc = nx.convert_node_labels_to_integers(H)
    gamma = float(np.linalg.eigvalsh(nx.laplacian_matrix(Hc, nodelist=list(Hc.nodes()))
                                     .toarray().astype(float))[1])
    return dict(n=n, m=m, lam=lam, x=x, y=y, fa=fa, fb=fb, da=da, db=db, Rpp=Rpp,
                Catt=Catt, Cdense=Cdense, gap=gap, fDf=fDf, S=S, core_var=core_var,
                mu=mu, gamma=gamma, dbar=float(dcore.mean()), Delta=float(dcore.max()))


def main():
    # regular cores => C_dense = 0 => gap = R'' + C_attach exactly
    print("=" * 90)
    print("EXACT pieces (verify) + joint R''+C_attach on REGULAR cores (C_dense≈0)")
    print("=" * 90)
    rC = rBeq = 0.0
    rows = []
    for m in [100, 200, 400]:
        for frac in [0.2, 0.35, 0.5, 0.7]:
            r = max(3, int(frac * m))
            if (r * m) % 2: r += 1
            H = nx.random_regular_graph(r, m, seed=3)
            q = analyze(H)
            rows.append((f"rr({m},{r})", q))
            # exact checks
            rC = max(rC, abs(q['Catt'] - ((q['da'] - 2) * q['fa'] * (q['fa'] - q['x'])
                                          + (q['db'] - 2) * q['fb'] * (q['fb'] - q['x']))))
            rBeq = max(rBeq, abs((2 - q['lam']) * q['x'] - q['y']))
    print(f"  exact C_attach formula residual : {rC:.2e}")
    print(f"  bottleneck (2-lam)x = y residual: {rBeq:.2e}")
    cdmax = max(abs(q['Cdense']) for _, q in rows)
    print(f"  max |C_dense| on regular cores  : {cdmax:.2e} (small; a,b have degree +1)")

    print("\n" + "=" * 90)
    print("leading cancellation + residual forms (regular cores, gap = R''+C_attach+C_dense)")
    print("=" * 90)
    print(f"  {'core':12s} {'q=dbar/n':>9} {'R''/x²':>8} {'|Catt|/x²':>10} {'gap/x²':>9} "
          f"{'gap/(2-λ)':>10} {'gap·m':>9} {'gap/corevar':>11}")
    for name, q in rows:
        x2 = q['x'] ** 2; qd = q['dbar'] / q['n']
        print(f"  {name:12s} {qd:9.3f} {q['Rpp']/x2:8.4f} {abs(q['Catt'])/x2:10.4f} {q['gap']/x2:9.5f} "
              f"{q['gap']/(2-q['lam']):10.4f} {q['gap']*q['m']:9.2f} "
              f"{q['gap']/max(q['core_var'],1e-12):11.3f}")

    print("\n" + "=" * 90)
    print("candidate residual forms — which is ~constant (×x²) across n at fixed frac?")
    print("=" * 90)
    # group by frac, vary n: does gap/(2-lam), gap*m, gap/core_var stabilize?
    from collections import defaultdict
    byfrac = defaultdict(list)
    for name, q in rows:
        byfrac[round(q['dbar'] / q['n'], 1)].append(q)
    for frac, qs in sorted(byfrac.items()):
        ns = [q['n'] for q in qs]
        g2lam = [q['gap'] / (2 - q['lam']) / q['x'] ** 2 for q in qs]
        gm = [q['gap'] * q['m'] / q['n'] for q in qs]   # gap*m/n
        print(f"  frac≈{frac}: n={ns}")
        print(f"     gap/((2-λ)x²) = {[round(v,3) for v in g2lam]}  (const? => gap ∝ (2-λ)x²)")
        print(f"     gap·m/n       = {[round(v,3) for v in gm]}  (const? => gap ∝ n/m)")

    print("\n" + "=" * 90)
    print("CHECK vs q=1: complete core (2-lam=0 but gap>0) -> gap NOT ∝ (2-lam)")
    print("=" * 90)
    for m in [100, 300]:
        q = analyze(nx.complete_graph(m))
        print(f"  K_{m}: 2-lam={2-q['lam']:.2e} gap={q['gap']:.5f} gap·m={q['gap']*q['m']:.3f} "
              f"(=10(n-3)={10*(q['n']-3)}?) Catt={q['Catt']:.2e}")

    print("\n" + "=" * 90)
    print("SUMMARY")
    print("=" * 90)
    print("  exact: C_attach=(d_a-2)f_a(f_a-x)+(d_b-2)f_b(f_b-x); (2-λ)x=y.  R''+C_attach exact via")
    print("  fDf,S splits.  Leading R''_inf=-C_attach_inf=2(1-q)x² cancel.  Residual gap is sub-leading;")
    print("  test above which candidate form (if any) it matches uniformly.")


if __name__ == "__main__":
    main()
