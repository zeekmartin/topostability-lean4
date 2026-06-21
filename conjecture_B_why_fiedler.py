"""
WHY does Lf=lam2 f imply fᵀMf = gap >= 0, when M = lam2 Q - (lam2/m) dd^T - L_t is indefinite?

gap = lam2 G - T (TRUE), T=triEnergy (apex form Σ_c E_{G[N(c)]}), lam2G = lam2(fᵀQf - S²/m).
Tasks: verify apex identity & SBP; per-apex slack distribution (local Poincaré fails ~6%);
M indefiniteness; K_n saturation; search for a non-negative (per-apex) decomposition of gap.
Run: python conjecture_B_why_fiedler.py
"""
import numpy as np
import networkx as nx


def setup(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f)
    return nodes, idx, n, A, d, L, lam, f, m, S


def apex_E(A, f, c):
    """E_{G[N(c)]}(f) = Σ_{a,b in N(c), a~b} (f_a-f_b)^2 (ordered double sum)."""
    nb = np.where(A[c] > 0)[0]
    tot = 0.0
    for a in nb:
        for b in nb:
            if A[a, b] > 0: tot += (f[a] - f[b]) ** 2
    return tot, nb


def main():
    print("=" * 86)
    print("TASK 1/3 — apex identity T=Σ_c E_c ; per-apex slack s_c = lam2·Σ_{N(c)}f² - E_c")
    print("=" * 86)
    print(f"  {'graph':14s} {'T':>9} {'Σ_c E_c':>9} {'match':>7} {'#s_c<0':>7} {'/n':>4} "
          f"{'Σs_c':>9} {'lam2fDf-T':>10}")
    for nm, G in [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
                  ("gnp30_.4", nx.gnp_random_graph(30, 0.4, seed=2)),
                  ("rr20_6", nx.random_regular_graph(6, 20, seed=1)),
                  ("deg2dense40", None), ("K20", nx.complete_graph(20))]:
        if nm == "deg2dense40":
            G = nx.gnp_random_graph(39, 0.65, seed=2); G.add_node(39); G.add_edge(39, 0); G.add_edge(39, 1)
        if not nx.is_connected(G): continue
        nodes, idx, n, A, d, L, lam, f, m, S = setup(G)
        A2 = A @ A
        T = sum(A2[idx[u], idx[v]] * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())  # unordered
        Tord = 2 * T
        sumE = 0.0; neg = 0; sumS = 0.0
        for c in range(n):
            E, nb = apex_E(A, f, c)
            sumE += E
            wc = sum(f[v] ** 2 for v in nb)           # Σ_{N(c)} f²
            sc = lam * wc - E
            sumS += sc
            if sc < -1e-9: neg += 1
        fDf = float(d @ (f * f))
        print(f"  {nm:14s} {Tord:9.3f} {sumE:9.3f} {str(abs(Tord-sumE)<1e-6):>7} {neg:7d} {n:4d} "
              f"{sumS:9.3f} {2*lam*fDf-Tord:10.3f}")
    print("  (T_ord = Σ_c E_c [apex identity]; s_c<0 = apices where LOCAL Poincaré fails; Σs_c=2λfDf-T_ord>=0)")

    print("\n" + "=" * 86)
    print("TASK 2 — SBP identity: Σ_e (σ_a+σ_b) f_a f_b = Σ_v σ_v (d_v - λ) f_v²  (σ_v = triangle deg)")
    print("=" * 86)
    for nm, G in [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
                  ("rr20_6", nx.random_regular_graph(6, 20, seed=1))]:
        nodes, idx, n, A, d, L, lam, f, m, S = setup(G)
        A2 = A @ A
        sig = np.array([sum(A2[i, j] for j in range(n) if A[i, j] > 0) for i in range(n)])  # σ_v
        lhs = sum((sig[idx[u]] + sig[idx[v]]) * f[idx[u]] * f[idx[v]] for u, v in G.edges())
        rhs = sum(sig[i] * (d[i] - lam) * f[i] ** 2 for i in range(n))
        print(f"  {nm:12s} LHS={lhs:.4f} RHS={rhs:.4f} match={abs(lhs-rhs)<1e-6}")
    print("  (SBP from Lf=λf: Σ_{u~v} f_u = (d_v-λ)f_v, weight-summed)")

    print("\n" + "=" * 86)
    print("TASK: M indefiniteness — M = λQ - (λ/m)ddᵀ - L_t; eigenvalues; f is NOT an M-eigenvector")
    print("=" * 86)
    for nm, G in [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)), ("K20", nx.complete_graph(20))]:
        nodes, idx, n, A, d, L, lam, f, m, S = setup(G)
        Q = np.diag(d) + A; A2 = A @ A
        Lt = np.zeros((n, n))                          # triangle Laplacian (weights t_e)
        for i in range(n):
            for j in range(n):
                if A[i, j] > 0: Lt[i, j] = -A2[i, j]
        for i in range(n): Lt[i, i] = -sum(Lt[i, j] for j in range(n) if j != i)
        M = lam * Q - (lam / m) * np.outer(d, d) - Lt
        mev = np.linalg.eigvalsh(M)
        nneg = int((mev < -1e-9).sum()); npos = int((mev > 1e-9).sum())
        fMf = float(f @ M @ f)
        Mf = M @ f; align = float(abs(f @ Mf) / (np.linalg.norm(f) * np.linalg.norm(Mf) + 1e-12))
        print(f"  {nm:12s} M eigvals: {nneg} neg, {npos} pos (INDEFINITE); fᵀMf={fMf:.4f}(=gap, >=0); "
              f"|cos(f,Mf)|={align:.3f} (f NOT M-eigvec unless ~1)")
    print("  => M is indefinite; gap=fᵀMf>=0 holds ONLY because f is pinned by Lf=λf (not generic).")

    print("\n" + "=" * 86)
    print("TASK 4 — K_n saturation: per-apex E_c, local slack, what's tight")
    print("=" * 86)
    for n in [8, 15]:
        G = nx.complete_graph(n); nodes, idx, _, A, d, L, lam, f, m, S = setup(G)
        c = 0; E, nb = apex_E(A, f, c); wc = sum(f[v] ** 2 for v in nb)
        print(f"  K{n}: lam2={lam:.1f}(=n) ; apex c=0: E_c={E:.4f} lam2·Σ_N(c)f²={lam*wc:.4f} "
              f"slack s_c={lam*wc-E:.4f}  (local Poincaré TIGHT at K_n? {abs(lam*wc-E)<1e-6})")
    print("  (at K_n, every apex's local graph is complete => local Poincaré is exactly tight => gap=0.)")

    print("\n" + "=" * 86)
    print("TASK 5 — is gap a SUM of nonneg per-apex terms? test gap_T := λ2fDf - T vs Σ_c max(s_c,0)")
    print("=" * 86)
    for nm, G in [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
                  ("deg2dense40", None), ("rr20_6", nx.random_regular_graph(6, 20, seed=1))]:
        if nm == "deg2dense40":
            G = nx.gnp_random_graph(39, 0.65, seed=2); G.add_node(39); G.add_edge(39, 0); G.add_edge(39, 1)
        if not nx.is_connected(G): continue
        nodes, idx, n, A, d, L, lam, f, m, S = setup(G)
        scs = []
        for c in range(n):
            E, nb = apex_E(A, f, c); wc = sum(f[v] ** 2 for v in nb); scs.append(lam * wc - E)
        scs = np.array(scs)
        print(f"  {nm:14s} Σs_c={scs.sum():.3f} (=2λfDf-T_ord) ; min s_c={scs.min():.4f} ; "
              f"Σmax(s_c,0)={np.maximum(scs,0).sum():.3f} ; Σmin(s_c,0)={np.minimum(scs,0).sum():.3f}")
    print("  (gap is NOT Σ nonneg per-apex: some s_c<0; the SOS must MIX apices — cancellation needed.)")

    print("\n" + "=" * 86)
    print("SUMMARY")
    print("=" * 86)
    print("  apex identity & SBP exact; M indefinite (gap>=0 only via Lf=λf pinning); K_n tight per-apex;")
    print("  gap NOT a per-apex nonneg sum (negative s_c => global cancellation = the open SOS).")


if __name__ == "__main__":
    main()
