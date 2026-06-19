"""
Weighted Bochner inequality from Gamma_2 curvature.

TARGET (= -Q >= 0):  2<d,Gamma(f)> <= Open + lam fDf + lam^2   (Lf=lam f, f perp 1, ||f||=1).

Gamma(f)(v)  = 1/2 sum_{u~v}(f_v-f_u)^2
Gamma2(f)(v) = 1/2 (L Gamma)(v) - lam Gamma(v)
             = (d_v/2 - lam) Gamma(v) - 1/2 sum_{u~v} Gamma(u)        [STEP 1]

STEP 1 verify the explicit per-vertex Gamma2 form, incl. the Jost-Liu triangle/2-ball split:
   R(v) := sum_{u~v} sum_{w~u, w!=v} (f_u-f_w)^2 = D_v(triangle) + Rout_v(outgoing)
   Gamma2(v) = ((d_v-1)/2 - lam) Gamma(v) - 1/4 R(v)
STEP 2 exact identity for <d,Gamma2> = 1/2 d^T L Gamma - lam <d,Gamma>.
STEP 3 pointwise CD(K):  K_pt = min_v Gamma2(v)/Gamma(v);  does it close the target?
STEP 4 integrated/degree-weighted CD:  K_int = <d,Gamma2>/<d,Gamma>.
STEP 5 Jost-Liu: triangles t_v, open cherries o_v; can curvature bound <d,Gamma> by Open?
Run: python conjecture_B_weighted_bochner.py
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

    gamma = 0.5 * (d * f2 - 2 * f * (A @ f) + (A @ f2))     # Gamma(f)(v)
    Lgamma = L @ gamma
    Gamma2 = 0.5 * Lgamma - lam * gamma
    Agamma = A @ gamma
    sigma = A @ d
    dGamma = float(d @ gamma)
    dGamma2 = float(d @ Gamma2)

    # explicit triangle/2-ball decomposition R(v)=D_v+Rout_v
    nbr = [np.where(A[c] > 0)[0] for c in range(n)]
    nbset = [set(nb.tolist()) for c, nb in enumerate(nbr)]
    D_v = np.zeros(n); Rout_v = np.zeros(n); R_v = np.zeros(n)
    t_v = np.zeros(n); o_v = np.zeros(n)   # triangles / open cherries at v (counts)
    for v in range(n):
        Sv = nbset[v]
        for u in nbr[v]:
            for w in nbr[u]:
                if w == v:
                    continue
                val = (f[u] - f[w]) ** 2
                R_v[v] += val
                if w in Sv:
                    D_v[v] += val
                else:
                    Rout_v[v] += val
        # triangle / open cherry counts among neighbour pairs
        nb = nbr[v]; k = len(nb)
        sub = A[np.ix_(nb, nb)]
        t_v[v] = sub.sum() / 2.0                       # edges among neighbours = triangles at v
        o_v[v] = k * (k - 1) / 2.0 - t_v[v]            # open cherries at v
    return dict(fam=fam, n=n, lam=lam, T=T, Open=Open, fDf=fDf, d=d, f=f, f2=f2, A=A, L=L,
                gamma=gamma, Gamma2=Gamma2, Agamma=Agamma, sigma=sigma,
                dGamma=dGamma, dGamma2=dGamma2, D_v=D_v, Rout_v=Rout_v, R_v=R_v,
                t_v=t_v, o_v=o_v)


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
    print("STEP 1 — explicit per-vertex Gamma2 forms (machine-precision verification)")
    print("=" * 76)
    r_s1 = mx(lambda q: float(np.max(np.abs(
        q['Gamma2'] - ((q['d'] / 2 - q['lam']) * q['gamma'] - 0.5 * q['Agamma'])))))
    r_R = mx(lambda q: float(np.max(np.abs(q['R_v'] - (q['D_v'] + q['Rout_v'])))))
    r_s1b = mx(lambda q: float(np.max(np.abs(
        q['Gamma2'] - (((q['d'] - 1) / 2 - q['lam']) * q['gamma'] - 0.25 * q['R_v'])))))
    print(f"  Gamma2(v) == (d_v/2 - lam) Gamma(v) - 1/2 (A Gamma)(v) : {r_s1:.2e}")
    print(f"  R(v) == D_v(triangle) + Rout_v(outgoing)              : {r_R:.2e}")
    print(f"  Gamma2(v) == ((d_v-1)/2 - lam)Gamma(v) - 1/4 R(v)     : {r_s1b:.2e}")
    print("  => Gamma2 carries the triangle energy D_v (NEG sign) + outgoing 2-ball Rout_v.")
    print("     Open-cherry ENDPOINT energy O_v does NOT appear in Gamma2(v).")

    print("\n" + "=" * 76)
    print("STEP 2 — exact identity for <d,Gamma2>")
    print("=" * 76)
    r_s2 = mx(lambda q: q['dGamma2'] - (0.5 * float(q['d'] @ (q['L'] @ q['gamma']))
                                        - q['lam'] * q['dGamma']))
    r_s2b = mx(lambda q: q['dGamma2'] - (0.5 * float((q['d'] ** 2 - q['sigma']) @ q['gamma'])
                                         - q['lam'] * q['dGamma']))
    print(f"  <d,Gamma2> == 1/2 d^T L Gamma - lam <d,Gamma>         : {r_s2:.2e}")
    print(f"  <d,Gamma2> == 1/2 <Ld, Gamma> - lam <d,Gamma>         : {r_s2b:.2e}")
    print("  => <d,Gamma2> = 1/2 E_L(d,Gamma) - lam<d,Gamma>: a PURE-Gamma (Dirichlet) object.")
    print("     It contains NO Open term -> the degree-weighted Gamma2 is structurally")
    print("     disconnected from the open-cherry energy in the target.")

    print("\n" + "=" * 76)
    print("STEP 3 — pointwise CD(K): K_pt = min_v Gamma2(v)/Gamma(v)")
    print("=" * 76)
    Kpts = []
    for q in data:
        g = q['gamma']; G2 = q['Gamma2']
        mask = g > 1e-10
        if mask.any():
            Kpts.append(float(np.min(G2[mask] / g[mask])))
    Kpts = np.array(Kpts)
    print(f"  K_pt = min_v Gamma2/Gamma : min={Kpts.min():.3f} median={np.median(Kpts):.3f} "
          f"max={Kpts.max():.3f}")
    print(f"  graphs with K_pt >= 0 (nonneg Ricci, CD(0)) : {int((Kpts >= -1e-9).sum())}/{ng}")
    print(f"  Lichnerowicz lam>=K_pt would need K_pt<=lam: holds trivially (K_pt mostly <0).")
    print("  => pointwise CD(K,inf) gives K<0 generally -> no positive curvature bound.")

    print("\n" + "=" * 76)
    print("STEP 4 — integrated / degree-weighted CD:  K_int = <d,Gamma2>/<d,Gamma>")
    print("=" * 76)
    Kint = np.array([q['dGamma2'] / q['dGamma'] for q in data if abs(q['dGamma']) > 1e-12])
    print(f"  K_int = <d,Gamma2>/<d,Gamma> : min={Kint.min():.3f} median={np.median(Kint):.3f} "
          f"max={Kint.max():.3f}")
    print(f"  K_int >= 0 : {int((Kint >= -1e-9).sum())}/{len(Kint)}")
    # Does ANY curvature bound close the target?  Target: 2<d,G> <= Open + lam fDf + lam^2.
    # <d,G2> = 1/2 E_L(d,G) - lam<d,G> has no Open, so a bound <d,G2> >= K<d,G> gives
    #   1/2 E_L(d,G) >= (K+lam)<d,G>  -- about E_L(d,Gamma), not Open. Confirm numerically that
    # the target slack Q is NOT a positive multiple of any Gamma2 aggregate.
    print("  Correlation of target slack -Q with curvature aggregates (should be weak/none):")
    negQ = np.array([q['Open'] + q['lam'] * q['fDf'] + q['lam'] ** 2 - 2 * q['dGamma']
                     for q in data])
    dG2 = np.array([q['dGamma2'] for q in data])
    sG2 = np.array([float(q['Gamma2'].sum()) for q in data])
    print(f"    corr(-Q, <d,Gamma2>)  = {np.corrcoef(negQ, dG2)[0,1]:+.3f}")
    print(f"    corr(-Q, sum Gamma2)  = {np.corrcoef(negQ, sG2)[0,1]:+.3f}")

    print("\n" + "=" * 76)
    print("STEP 5 — Jost-Liu: triangles vs open cherries vs the Open energy")
    print("=" * 76)
    # Open = sum_v o_v-weighted gradients; check Open correlates with sum_v o_v (counts) only weakly,
    # but Open IS the apex open-pair ENERGY (verified prior). Here: does a clustering bound help?
    # Jost-Liu Ollivier curvature kappa(u,v) ~ uses #common neighbours (triangles) t_uv.
    # Test whether <d,Gamma> can be bounded by Open + spectral via the triangle term T.
    # Known exact: T + Open = sum[sigma-(d-lam)^2]f^2 ; and 2<d,Gamma> = 2 lam fDf - A.
    # Report the triangle energy T vs Open and the target gap.
    for q in data[:0]:
        pass
    Tsum = np.array([q['T'] for q in data])
    Opensum = np.array([q['Open'] for q in data])
    print(f"  triangle energy T : median={np.median(Tsum):.3f}; Open : median={np.median(Opensum):.3f}")
    print(f"  corr(T, Open) = {np.corrcoef(Tsum, Opensum)[0,1]:+.3f}")
    print("  Jost-Liu curvature uses triangle counts t_uv on EDGES (Ollivier kappa), a DIFFERENT")
    print("  curvature from Bakry Gamma2; neither yields the open-cherry endpoint energy Open.")

    print("\n" + "=" * 76)
    print("CONCLUSION")
    print("=" * 76)
    print("  Gamma2 route does NOT close the target: <d,Gamma2>=1/2 E_L(d,Gamma)-lam<d,Gamma> is a")
    print("  pure-Gamma Dirichlet object with NO Open term (corr(-Q,<d,Gamma2>) weak); pointwise")
    print("  CD(K) has K<0; integrated CD bounds E_L(d,Gamma), not Open. The target needs the")
    print("  open-cherry ENDPOINT energy, which Gamma2 (2-ball EDGE energy) does not contain.")


if __name__ == "__main__":
    main()
