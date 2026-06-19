"""
S-procedure / Lagrange certificate for  gap = lam2 G - B2' >= 0  (f Fiedler, Lf=lam2 f, f perp 1).

gap = f^T M f,  M = lam2 (D+A) - (lam2/m) d d^T - L_min,  L_min = Laplacian with edge weights
  w_e = min(d_a,d_b) - 1.  (Check: M 1 = 0, f^T M f = gap.)
Constraint (L - lam2 I) f = 0.  For scalar alpha,  M_alpha := M + alpha (L - lam2 I)  has
  f^T M_alpha f = gap  (the alpha-term vanishes on f).  If M_alpha is PSD on 1-perp, then gap>=0.

TASK1/2 min alpha* (scalar) making M_alpha PSD on 1-perp; structure of alpha*.
TASK3 diagonal multiplier beta = c d.
TASK4 deg2+dense alpha*(n) scaling.
TASK5 regular: alpha = d+lam2-1 gives M_alpha|_perp = gap * I (manifestly PSD).
Run: python conjecture_B_sdp_certificate.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques
from conjecture_B_B2prime_scaling import deg2_dense


def build(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1)
    L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges()
    Wmin = np.zeros((n, n))
    for a, b in [(idx[u], idx[v]) for u, v in G.edges()]:
        w = min(d[a], d[b]) - 1
        Wmin[a, b] = w; Wmin[b, a] = w
    L_min = np.diag(Wmin.sum(1)) - Wmin
    Q = np.diag(d) + A
    M = lam * Q - (lam / m) * np.outer(d, d) - L_min
    # 1-perp basis
    P = np.eye(n) - np.ones((n, n)) / n
    wp, Vp = np.linalg.eigh(P)
    B = Vp[:, wp > 0.5]                       # n x (n-1), orthonormal basis of 1-perp
    gap = float(f @ M @ f)
    LmI = L - lam * np.eye(n)
    return dict(n=n, m=m, lam=lam, d=d, f=f, L=L, M=M, LmI=LmI, B=B, gap=gap,
                dmax=float(d.max()), dbar=float(d.mean()), regular=bool(np.allclose(d, d[0])),
                M1=float(np.abs(M @ np.ones(n)).max()))


def mineig_perp(q, alpha):
    Mr = q['B'].T @ (q['M'] + alpha * q['LmI']) @ q['B']
    return float(np.linalg.eigvalsh(Mr)[0])


def alpha_star(q, hi=None):
    if mineig_perp(q, 0.0) >= -1e-9:
        return 0.0
    if hi is None:
        hi = 20 * (q['dmax'] + q['lam'] + 1)
    lo = 0.0
    # ensure feasible at hi
    grow = 0
    while mineig_perp(q, hi) < -1e-9 and grow < 40:
        hi *= 2; grow += 1
    for _ in range(60):
        mid = (lo + hi) / 2
        if mineig_perp(q, mid) >= -1e-9:
            hi = mid
        else:
            lo = mid
    return hi


def graphs():
    out = []
    for fam, G in ([("corpus", g) for _, g in corpus()]
                   + [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (3, 60))]
                   + [("chain", chain_cliques(mm, k)) for mm, k in ((10, 2), (20, 2), (15, 4))]):
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        ev = np.linalg.eigvalsh(nx.laplacian_matrix(G, nodelist=list(G.nodes()))
                                .toarray().astype(float))
        if ev[1] < 1e-9:
            continue
        out.append(G)
    return out


def main():
    data = [build(G) for G in graphs()]
    ng = len(data)
    print(f"{ng} graphs;  max |M*1| = {max(q['M1'] for q in data):.2e}  (M annihilates 1)\n")

    # ---------- TASK 1/2 ----------
    print("=" * 78)
    print("TASK 1/2 — scalar alpha*: min alpha with M + alpha(L-lam2 I) PSD on 1-perp")
    print("=" * 78)
    feas = 0; astars = []; ratΔ = []; ratbar = []
    for q in data:
        a = alpha_star(q)
        astars.append(a)
        if mineig_perp(q, a) >= -1e-7:
            feas += 1
        ratΔ.append(a / (q['dmax'] + q['lam'] - 1) if q['dmax'] + q['lam'] - 1 > 1e-9 else np.nan)
        ratbar.append(a / (q['dbar'] + q['lam'] - 1) if q['dbar'] + q['lam'] - 1 > 1e-9 else np.nan)
    astars = np.array(astars)
    print(f"  scalar certificate feasible : {feas}/{ng}  (alpha* always finite when gap>0)")
    print(f"  alpha* : min={astars.min():.3f} median={np.median(astars):.3f} max={astars.max():.3f}")
    print(f"  alpha*/(Δ+lam2-1) : median={np.nanmedian(ratΔ):.3f} max={np.nanmax(ratΔ):.3f}")
    print(f"  alpha*/(dbar+lam2-1): median={np.nanmedian(ratbar):.3f} max={np.nanmax(ratbar):.3f}")

    # test EXPLICIT alpha candidates
    print("\n  explicit alpha candidates — does M_alpha PSD on 1-perp hold?")
    for name, af in [("Δ+lam2-1", lambda q: q['dmax'] + q['lam'] - 1),
                     ("dbar+lam2-1", lambda q: q['dbar'] + q['lam'] - 1),
                     ("2Δ", lambda q: 2 * q['dmax']),
                     ("Δ", lambda q: q['dmax'])]:
        ok = sum(1 for q in data if mineig_perp(q, af(q)) >= -1e-7)
        print(f"    alpha = {name:14s}: PSD on 1-perp for {ok}/{ng}")

    # ---------- TASK 5 ----------
    print("\n" + "=" * 78)
    print("TASK 5 — regular graphs: alpha = d+lam2-1 gives M_alpha|perp = gap * I")
    print("=" * 78)
    for name, Gr in [("C20", nx.cycle_graph(20)), ("Petersen", nx.petersen_graph()),
                     ("K8", nx.complete_graph(8)), ("Q4", nx.hypercube_graph(4)),
                     ("K33", nx.complete_bipartite_graph(3, 3))]:
        q = build(Gr); d0 = q['d'][0]; al = d0 + q['lam'] - 1
        Mr = q['B'].T @ (q['M'] + al * q['LmI']) @ q['B']
        evs = np.linalg.eigvalsh(Mr)
        isscalar = np.allclose(evs, q['gap'], atol=1e-6)
        print(f"  {name:9s} reg={q['regular']} d={d0:.0f} lam2={q['lam']:.3f} alpha={al:.3f} "
              f"gap={q['gap']:.4f} M_alpha|perp eig in[{evs.min():.4f},{evs.max():.4f}] "
              f"= gap*I? {isscalar}")

    # ---------- TASK 4 ----------
    print("\n" + "=" * 78)
    print("TASK 4 — deg2+dense: alpha*(n) scaling and explicit-alpha feasibility")
    print("=" * 78)
    ns = [10, 20, 50, 100, 200]
    print(f"  {'n':>5} {'gap':>9} {'alpha*':>9} {'Δ':>6} {'Δ+lam2-1':>10} {'PSD@Δ+lam2-1':>13}")
    arows = []
    for n in ns:
        q = build(deg2_dense(n)); a = alpha_star(q); arows.append((n, a))
        psd = mineig_perp(q, q['dmax'] + q['lam'] - 1) >= -1e-7
        print(f"  {n:5d} {q['gap']:9.5f} {a:9.4f} {q['dmax']:6.0f} {q['dmax']+q['lam']-1:10.3f} "
              f"{str(psd):>13}")
    nsa = np.array([r[0] for r in arows]); aa = np.array([r[1] for r in arows])
    if np.all(aa > 0):
        sl = np.polyfit(np.log(nsa), np.log(aa), 1)[0]
        print(f"    alpha* ~ n^{sl:.3f}  (grows with n -> not a uniform constant)")

    # ---------- TASK 3 ----------
    print("\n" + "=" * 78)
    print("TASK 3 — diagonal multiplier beta = c*d  (anticommutator)")
    print("=" * 78)
    # M + c(diag(d)(L-lam I)+(L-lam I)diag(d)) PSD on 1-perp for some c? test grid of c.
    def mineig_diag(q, c):
        D = np.diag(q['d'])
        Mc = q['M'] + c * (D @ q['LmI'] + q['LmI'] @ D)
        Mr = q['B'].T @ Mc @ q['B']
        return float(np.linalg.eigvalsh(Mr)[0])
    feasd = 0
    for q in data:
        cs = np.linspace(0, 3, 31)
        if any(mineig_diag(q, c) >= -1e-7 for c in cs):
            feasd += 1
    print(f"  diagonal beta=c*d feasible (some c in [0,3]) : {feasd}/{ng}")
    # on deg2dense does small constant c work?
    for n in [20, 50, 100]:
        q = build(deg2_dense(n))
        best = min((abs(c) for c in np.linspace(0, 3, 61) if mineig_diag(q, c) >= -1e-7),
                   default=None)
        print(f"    deg2dense n={n}: smallest c in [0,3] with PSD = {best}")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print(f"  Scalar S-procedure: feasible {feas}/{ng}; alpha* ~ Δ+lam2-1 (median ratio "
          f"{np.nanmedian(ratΔ):.2f}). Regular: alpha=d+lam2-1 gives M_alpha|perp = gap*I exactly.")
    print("  alpha* GROWS with n on deg2+dense (~Δ~n): not a uniform constant, but the explicit")
    print("  alpha = Δ+lam2-1 is the candidate uniform multiplier — see feasibility counts above.")


if __name__ == "__main__":
    main()
