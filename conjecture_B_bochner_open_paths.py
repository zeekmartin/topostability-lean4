"""
Is the open-2-path energy a Gamma_2 / Bochner term?

Conventions (combinatorial L = D - A, L f = lam f, f unit Fiedler):
  Gamma(f)(v)   = 1/2 sum_{u~v} (f_v - f_u)^2                      (carre du champ)
  Gamma(f,g)(v) = 1/2 sum_{u~v} (f_v - f_u)(g_v - g_u)
  Gamma2(f)(v)  = 1/2 [ L Gamma(f)(v) - 2 Gamma(f, L f)(v) ]
               = 1/2 (L Gamma(f))(v) - lam Gamma(f)(v)            (eigenvector)
where (L Gamma(f)) is L applied to the vector v |-> Gamma(f)(v).

Known: A := Cov_L(d,f^2) = d^T L(f o f) = 2 lam fDf - 2 <d,Gamma(f)>,
       L(f^2) = 2 lam f^2 - 2 Gamma(f)  (pointwise, eigenvector).
Target: Open + A >= lam fAf   (fAf = fDf - lam).

TASK 1 compute <d,Gamma>, sum Gamma2, Open, etc.
TASK 2 exact identities among Open, <d,Gamma>, lam fDf, lam fAf, Gamma2 terms.
TASK 3 is Open = / <= a curvature term <d,Gamma> - something?
TASK 4 per-vertex Gamma2 vs apex open/closed-pair energies (non-adjacent neighbour pairs).
Run: python conjecture_B_bochner_open_paths.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(fam, G):
    nodes = list(G.nodes())
    n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    A = np.diag(d) - L
    m = G.number_of_edges()
    ev, V = np.linalg.eigh(L)
    lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    f2 = f * f
    A2 = A @ A
    M = A * A2
    P = A2 - np.diag(d) - M
    L_M = np.diag(M.sum(1)) - M
    L_P = np.diag(P.sum(1)) - P
    T = float(f @ L_M @ f)
    Open = float(f @ L_P @ f)
    fDf = float(d @ f2)
    fAf = float(f @ A @ f)
    S = float(d @ f)

    # carre du champ Gamma(f)(v) = 1/2 sum_{u~v}(f_v-f_u)^2
    gamma = 0.5 * (d * f2 - 2 * f * (A @ f) + (A @ f2))
    Lgamma = L @ gamma
    Gamma2 = 0.5 * Lgamma - lam * gamma         # eigenvector form
    dGamma = float(d @ gamma)
    dGamma2 = float(d @ Gamma2)
    sumGamma = float(gamma.sum())
    sumGamma2 = float(Gamma2.sum())
    Acal = 2 * lam * fDf - 2 * dGamma           # = Cov_L(d,f^2)

    # apex (neighbourhood) pair energies, ordered; sum_x O_x=2 Open, sum_x D_x=2 T
    O_x = np.zeros(n); D_x = np.zeros(n); full_x = np.zeros(n)
    nbr = [np.where(A[c] > 0)[0] for c in range(n)]
    for c in range(n):
        nb = nbr[c]
        fc = f[nb]
        sub = A[np.ix_(nb, nb)]
        g2 = np.subtract.outer(fc, fc) ** 2
        D_x[c] = float((sub * g2).sum())
        full_x[c] = float(g2.sum())             # = 2(d_c mass_c - s_c^2)
        O_x[c] = full_x[c] - D_x[c]
    return dict(fam=fam, n=n, lam=lam, T=T, Open=Open, fDf=fDf, fAf=fAf, S=S, m=m,
                gamma=gamma, Gamma2=Gamma2, dGamma=dGamma, dGamma2=dGamma2,
                sumGamma=sumGamma, sumGamma2=sumGamma2, Acal=Acal,
                O_x=O_x, D_x=D_x, full_x=full_x, d=d, f=f, f2=f2, A=A, L=L)


def all_graphs():
    gs = [("corpus", G) for _, G in corpus()]
    gs += [("barbell", nx.barbell_graph(m, Lb)) for m in (5, 20, 40, 80) for Lb in (0, 1, 3)]
    gs += [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (40, 40), (3, 60))]
    gs += [("chain", chain_cliques(m, k)) for m, k in ((10, 2), (20, 2), (40, 2), (15, 4))]
    out = []
    for fam, G in gs:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        ev = np.linalg.eigvalsh(nx.laplacian_matrix(G, nodelist=list(G.nodes()))
                                .toarray().astype(float))
        if ev[1] < 1e-9:
            continue
        out.append((fam, G))
    return out


def main():
    data = [graph_quant(fam, G) for fam, G in all_graphs()]
    ng = len(data)
    print(f"{ng} graphs\n")

    def mx(fn):
        return max(abs(fn(q)) for q in data)

    print("=" * 76)
    print("TASK 1/2 — exact identities (residuals over all graphs)")
    print("=" * 76)
    r_sg = mx(lambda q: q['sumGamma'] - q['lam'])
    r_sg2 = mx(lambda q: q['sumGamma2'] + q['lam'] ** 2)
    r_dG = mx(lambda q: q['dGamma'] - 0.5 * sum(
        (q['d'][a] + q['d'][b]) * (q['f'][a] - q['f'][b]) ** 2
        for a in range(q['n']) for b in range(q['n']) if q['A'][a, b] > 0) / 2)
    # NOTE the /2 above: the double loop counts ordered pairs; 1/2*ordered = unordered edge sum.
    r_A = mx(lambda q: q['Acal'] - (2 * q['lam'] * q['fDf'] - 2 * q['dGamma']))
    r_boch = mx(lambda q: float(np.max(np.abs(q['L'] @ q['f2'] - (2 * q['lam'] * q['f2'] - 2 * q['gamma'])))))
    print(f"  sum_v Gamma(f)(v) == lam (= fLf)              : {r_sg:.2e}")
    print(f"  sum_v Gamma2(f)(v) == -lam^2                  : {r_sg2:.2e}")
    print(f"  <d,Gamma> == 1/2 sum_E (d_a+d_b)(f_a-f_b)^2   : {r_dG:.2e}")
    print(f"  A == 2 lam fDf - 2 <d,Gamma>                  : {r_A:.2e}")
    print(f"  pointwise L(f^2) == 2 lam f^2 - 2 Gamma(f)    : {r_boch:.2e}")

    # The target as a curvature inequality:
    #   -Q = Open + A - lam fAf ; substitute A = 2 lam fDf - 2<d,Gamma>:
    #   -Q = Open + 2 lam fDf - 2<d,Gamma> - lam(fDf-lam)
    #      = Open + lam fDf + lam^2 - 2<d,Gamma>
    r_negQ = mx(lambda q: (q['Open'] + q['lam'] * q['fDf'] + q['lam'] ** 2 - 2 * q['dGamma'])
                - (q['Open'] + q['Acal'] - q['lam'] * q['fAf']))
    print(f"  -Q == Open + lam fDf + lam^2 - 2<d,Gamma>     : {r_negQ:.2e}")
    print("  => TARGET  <=>  2<d,Gamma(f)> <= Open + lam fDf + lam^2")
    print("     (degree-weighted Dirichlet energy <= open energy + spectral terms)")

    print("\n" + "=" * 76)
    print("TASK 2b — <d,Gamma2> and Gamma2 aggregates (search for Open)")
    print("=" * 76)
    # explore clean forms for <d,Gamma2>
    for name, fn in [
        ("<d,Gamma2>", lambda q: q['dGamma2']),
        ("sum Gamma2 (=-lam^2)", lambda q: q['sumGamma2']),
        ("lam^2", lambda q: q['lam'] ** 2),
        ("lam<d,Gamma>", lambda q: q['lam'] * q['dGamma']),
    ]:
        vals = np.array([fn(q) for q in data])
        print(f"  {name:24s}: min={vals.min():.4f} median={np.median(vals):.4f} max={vals.max():.4f}")
    # test candidate: <d,Gamma2> ?= 1/2 dLgamma - lam<d,gamma>; and any tie to Open
    # regress Open on {<d,Gamma>, <d,Gamma2>, lam fDf, lam^2} per graph is not const-coef;
    # instead report Open vs <d,Gamma> ratio and vs the curvature excess.
    print("\n" + "=" * 76)
    print("TASK 3 — Open vs the curvature term <d,Gamma(f)>")
    print("=" * 76)
    rO = np.array([q['Open'] / q['dGamma'] for q in data if q['dGamma'] > 1e-12])
    print(f"  Open / <d,Gamma>  : min={rO.min():.4f} median={np.median(rO):.3f} max={rO.max():.3f}")
    # excess curvature E := 2<d,Gamma> - lam fDf - lam^2 ; target Open >= E
    exc = np.array([2 * q['dGamma'] - q['lam'] * q['fDf'] - q['lam'] ** 2 for q in data])
    okE = sum(1 for q in data if q['Open'] >= (2 * q['dGamma'] - q['lam'] * q['fDf'] - q['lam'] ** 2) - 1e-7)
    print(f"  curvature excess E=2<d,Gamma>-lam fDf-lam^2: min={exc.min():.3f} max={exc.max():.3f}")
    print(f"  Open >= E (== the conjecture -Q>=0): {okE}/{ng}")
    # is Open <= <d,Gamma>?  (is open energy below the degree-weighted Dirichlet energy?)
    le = sum(1 for q in data if q['Open'] <= q['dGamma'] + 1e-9)
    print(f"  Open <= <d,Gamma> ? {le}/{ng}")

    print("\n" + "=" * 76)
    print("TASK 4 — per-vertex Gamma2 vs apex open/closed-pair energies")
    print("=" * 76)
    # apex: full_x = O_x + D_x = sum_{y,z in N(x)}(f_y-f_z)^2 (ordered) = 2(d_x mass_x - s_x^2).
    # Does Gamma2(f)(x) contain (1/2)*open part O_x/... ? Fit Gamma2_x to local features pooled.
    feats = {}
    Y = np.concatenate([q['Gamma2'] for q in data])
    cand = {
        'O_x (open pairs)': np.concatenate([q['O_x'] for q in data]),
        'D_x (closed pairs)': np.concatenate([q['D_x'] for q in data]),
        'full_x': np.concatenate([q['full_x'] for q in data]),
        'gamma_x': np.concatenate([q['gamma'] for q in data]),
        'lam*f_x^2': np.concatenate([q['lam'] * q['f2'] for q in data]),
        'lam*gamma_x': np.concatenate([q['lam'] * q['gamma'] for q in data]),
    }
    # correlations of Gamma2_x with each candidate (pooled)
    for name, X in cand.items():
        if X.std() > 1e-12 and Y.std() > 1e-12:
            c = np.corrcoef(X, Y)[0, 1]
            print(f"  corr(Gamma2_x, {name:20s}) = {c:+.3f}")
    # aggregate: is sum_x [Gamma2_x restricted to ...] = Open? Test the natural candidate that the
    # non-adjacent-neighbour part of the on-graph Hessian is the open energy.  Compute the explicit
    # 'incomplete-neighbourhood' term  I_x := (1/2) O_x  and compare sum to Open.
    sumO = sum(q['O_x'].sum() for q in data)
    sumOpen = sum(2 * q['Open'] for q in data)
    print(f"  sum_x O_x  == 2*Open (apex open-pair = open energy): "
          f"residual {abs(sumO - sumOpen):.2e}")
    print("  => Open IS exactly the apex non-adjacent-neighbour-pair energy (incomplete N(x));")
    print("     this is the term Gamma2 acquires when neighbourhoods are not cliques.")

    print("\n" + "=" * 76)
    print("SUMMARY")
    print("=" * 76)
    print("  EXACT: Sum Gamma=lam; Sum Gamma2=-lam^2; <d,Gamma>=1/2 Sum_E(d_a+d_b)(f_a-f_b)^2;")
    print("         A=2lam fDf-2<d,Gamma>; L(f^2)=2lam f^2-2Gamma; ")
    print("         -Q = Open + lam fDf + lam^2 - 2<d,Gamma>  (TARGET <=> 2<d,Gamma> <= Open+lam fDf+lam^2)")


if __name__ == "__main__":
    main()
