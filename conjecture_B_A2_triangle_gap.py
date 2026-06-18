"""
The A^2-to-triangle Hadamard gap, via the 2-path Laplacian split.

Entrywise (A^2)_ab = #common neighbours of a,b.  Split 2-paths a-c-b by adjacency of endpoints:
    A^2 = diag(d) + M + P
      M_ab = t_ab * [a~b]              CLOSED 2-paths  = triangle edges  (Hadamard A o A^2)
      P_ab = (A^2)_ab * [a not~b]      OPEN   2-paths
2-path Laplacian  L2 = diag(sigma) - A^2,  sigma_v = sum_{c~v} d_c = (A d)_v,  splits as
    L2 = L_M + L_P
      L_M = diag(tau) - M              triangle Laplacian,  tau_v = sum_{u~v} t_vu
      L_P = diag(sigma-d-tau) - P      open-2-path Laplacian  (both PSD)

Eigen-recursion (Af = (D-lam)f):  f^T A^2 f = sum_c (sum_{a in N(c)} f_a)^2 = sum_v (d_v-lam)^2 f_v^2.

MASTER IDENTITY (exact):  T + Open = sum_v [sigma_v - (d_v-lam)^2] f_v^2,   T,Open >= 0.
  T    = f^T L_M f  = triangle energy
  Open = f^T L_P f  = open-2-path Dirichlet energy (nonnegative remainder)

REFORMULATION:  aggregate Poincare  T <= lam sum d_v f_v^2
            <=> Open >= sum_v [sigma_v - (d_v-lam)^2 - lam d_v] f_v^2.

Run: python conjecture_B_A2_triangle_gap.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def quantities(G):
    nodes = list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    diagd = np.diag(d)
    M = A * A2                      # closed 2-paths (triangle edges)
    P = A2 - diagd - M              # open 2-paths
    sigma = A @ d                   # sum of neighbour degrees
    tau = M.sum(1)
    L_M = np.diag(tau) - M
    L_P = np.diag((A2 - diagd - M).sum(1)) - P
    L2 = np.diag(sigma) - A2

    s = A @ f                        # s_c = sum_{a in N(c)} f_a = (Af)_c
    T = float(f @ L_M @ f)
    Open = float(f @ L_P @ f)
    fA2f = float(f @ A2 @ f)
    fDf = float((d * f * f).sum())

    return dict(
        lam=lam, T=T, Open=Open, fDf=fDf,
        # exact identity residuals
        r_A2split=float(np.max(np.abs(A2 - (diagd + M + P)))),
        r_L2split=float(np.max(np.abs(L2 - (L_M + L_P)))),
        r_apex=float(abs(fA2f - (s * s).sum())),                       # f^T A^2 f = sum_c s_c^2
        r_eigen=float(abs(fA2f - ((d - lam) ** 2 * f * f).sum())),     # = sum (d-lam)^2 f^2
        r_master=float(abs((T + Open) - ((sigma - (d - lam) ** 2) * f * f).sum())),
        # nonnegativity
        Open_min_eig=float(np.linalg.eigvalsh(L_P).min()),
        LM_min_eig=float(np.linalg.eigvalsh(L_M).min()),
        Open_val=Open,
        # reformulation slack  (== -Q)
        reform_slack=float(Open - ((sigma - (d - lam) ** 2 - lam * d) * f * f).sum()),
        Q=float(T - lam * fDf),
    )


def main():
    graphs = [G for _, G in corpus()]
    graphs += [nx.barbell_graph(m, Lb) for m in (5, 20, 40, 80) for Lb in (0, 1, 3)]
    graphs += [glue(a, b) for a, b in ((5, 5), (20, 20), (40, 40), (3, 60))]
    graphs += [chain_cliques(m, k) for m, k in ((10, 2), (20, 2), (40, 2), (15, 4))]

    acc = {}
    for G in graphs:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        ev = np.linalg.eigvalsh(nx.laplacian_matrix(G, nodelist=list(G.nodes()))
                                .toarray().astype(float))
        if ev[1] < 1e-9:
            continue
        for k, v in quantities(G).items():
            acc.setdefault(k, []).append(v)

    n = len(acc['Q'])
    print("=" * 78)
    print(f"graphs analysed: {n}")
    print("\n--- EXACT IDENTITY RESIDUALS (want machine zero) ---")
    print(f"  A^2 = diag(d) + M + P                 : max={np.max(acc['r_A2split']):.2e}")
    print(f"  L2  = L_M + L_P                       : max={np.max(acc['r_L2split']):.2e}")
    print(f"  f^T A^2 f = sum_c s_c^2  (apex sum)   : max={np.max(acc['r_apex']):.2e}")
    print(f"  f^T A^2 f = sum_v (d-lam)^2 f^2       : max={np.max(acc['r_eigen']):.2e}")
    print(f"  T + Open = sum_v[sigma-(d-lam)^2]f^2  : max={np.max(acc['r_master']):.2e}")

    print("\n--- NONNEGATIVITY (both are graph-Laplacian energies) ---")
    print(f"  L_M PSD  (min eigenvalue)             : min={np.min(acc['LM_min_eig']):.2e}")
    print(f"  L_P PSD  (min eigenvalue)             : min={np.min(acc['Open_min_eig']):.2e}")
    print(f"  Open = f^T L_P f >= 0                 : min={np.min(acc['Open_val']):.4f}")

    print("\n--- REFORMULATION:  aggregate Poincare <=> Open >= sum[sigma-(d-lam)^2-lam d]f^2 ---")
    sl = np.array(acc['reform_slack']); Q = np.array(acc['Q'])
    print(f"  reformulation slack (== -Q)           : min={sl.min():.4f}  median={np.median(sl):.3f}")
    print(f"  aggregate Poincare Q<=0 holds         : {int((Q <= 1e-9).sum())}/{n}")
    print("=" * 78)


if __name__ == "__main__":
    main()
