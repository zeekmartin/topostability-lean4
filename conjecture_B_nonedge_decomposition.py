"""
Non-edge decomposition of gap = lam2 G - T (vanishes only at K_n).

Key identities to use:
  - Complement: L_Gbar = nI - J - L_G; for f perp 1, L_Gbar f = (n-lam) f  =>  Sum_{nonedge} g^2 = n - lam.
  - t_ab = (n-2) - deficit_ab, deficit_ab = #{c != a,b : c !~ a or c !~ b}  =>  T = (n-2)lam - Sum_e deficit_e g_e^2.
Goal: gap = Sum_{nonedge ij} Phi_ij ?  test sign/PSD/covariance.
Run: python conjecture_B_nonedge_decomposition.py
"""
import numpy as np
import networkx as nx


def Q(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f)); A2 = A @ A
    T = sum(A2[idx[u], idx[v]] * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (2 * fDf - lam - S ** 2 / m) - T
    # complement
    Abar = (np.ones((n, n)) - np.eye(n)) - A
    Lbar = np.diag(Abar.sum(1)) - Abar
    fbar = float(f @ Lbar @ f)                       # = Sum_nonedge g^2 (should = n-lam)
    nonedges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] == 0]
    sum_g2_ne = sum((f[i] - f[j]) ** 2 for i, j in nonedges)
    # deficit form of T
    defT = 0.0
    for u, v in G.edges():
        a, b = idx[u], idx[v]
        deficit = sum(1 for c in range(n) if c != a and c != b and (A[a, c] == 0 or A[b, c] == 0))
        defT += deficit * (f[a] - f[b]) ** 2
    T_def = (n - 2) * lam - defT
    return dict(n=n, idx=idx, A=A, d=d, lam=lam, f=f, m=m, S=S, fDf=fDf, T=T, gap=gap,
                fbar=fbar, sum_g2_ne=sum_g2_ne, nonedges=nonedges, defT=defT, T_def=T_def, A2=A2,
                Abar=Abar)


def corpus():
    out = [("K20-e", _Kme(20)), ("K30-e", _Kme(30)),
           ("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
           ("gnp30_.4", nx.gnp_random_graph(30, 0.4, seed=2)),
           ("gnp20_.8", nx.gnp_random_graph(20, 0.8, seed=3)),
           ("rr20_6", nx.random_regular_graph(6, 20, seed=1)),
           ("rr30_10", nx.random_regular_graph(10, 30, seed=1)),
           ("cycle20", nx.cycle_graph(20))]
    H = nx.gnp_random_graph(39, 0.65, seed=2); H.add_node(39); H.add_edge(39, 0); H.add_edge(39, 1)
    out.append(("deg2dense40", H))
    return [(nm, G) for nm, G in out if nx.is_connected(G)]


def _Kme(n):
    G = nx.complete_graph(n); G.remove_edge(0, 1); return G


def main():
    data = [(nm, Q(G)) for nm, G in corpus()]

    print("=" * 92)
    print("TASK 1/4 — complement eigenvector: Sum_{nonedge} g^2 = n - lam (f is L_Gbar-eigvec)")
    print("=" * 92)
    for nm, q in data:
        print(f"  {nm:12s} Sum_nonedge g²={q['sum_g2_ne']:9.4f}  fᵀL_Ḡf={q['fbar']:9.4f}  "
              f"n-λ={q['n']-q['lam']:9.4f}  match={abs(q['sum_g2_ne']-(q['n']-q['lam']))<1e-6}")

    print("\n" + "=" * 92)
    print("TASK 2/3 — T = (n-2)λ - Σ_e deficit_e g_e²  (deficit = missing-adjacency count)")
    print("=" * 92)
    for nm, q in data:
        print(f"  {nm:12s} T={q['T']:10.4f}  (n-2)λ-Σdef·g²={q['T_def']:10.4f}  "
              f"match={abs(q['T']-q['T_def'])<1e-6}")

    print("\n" + "=" * 92)
    print("TASK 5 — gap in complement form. gap = λ₂G - (n-2)λ + Σ_e deficit_e g_e²")
    print("   λ₂G-(n-2)λ = λ(2fDf-λ-S²/m-(n-2)). Express via nonedges & test gap=Σ_nonedge Φ_ij")
    print("=" * 92)
    print(f"  {'graph':12s} {'gap':>9} {'Σ_e def·g²':>11} {'λ₂G-(n-2)λ':>12} {'#nonedge':>9}")
    for nm, q in data:
        bracket = q['lam'] * (2 * q['fDf'] - q['lam'] - q['S'] ** 2 / q['m'] - (q['n'] - 2))
        print(f"  {nm:12s} {q['gap']:9.4f} {q['defT']:11.4f} {bracket:12.4f} {len(q['nonedges']):9d}")
    print("  (gap = bracket + Σ_e deficit·g²; both pieces; deficit term >=0, bracket sign?)")

    print("\n" + "=" * 92)
    print("TASK 5b — candidate per-nonedge Φ_ij. Try Φ_ij from gap distributed over nonedges")
    print("=" * 92)
    # Candidate: using L_Gbar f=(n-lam)f, build a complement-based decomposition.
    # gap/#nonedge (uniform) and test if a natural Phi_ij (e.g. involving g_ij^2 nonedge) reconstructs gap.
    for nm, q in data:
        ne = q['nonedges']; f = q['f']; A = q['A']; A2 = q['A2']; n = q['n']; lam = q['lam']
        if not ne:
            print(f"  {nm:12s} (complete, no nonedges; gap={q['gap']:.4f})"); continue
        # per-nonedge "complement triangle" weight: tbar_ij = common NON-neighbors? test correlation
        gap = q['gap']
        # candidate A: gap ?= sum_nonedge lam * g_ij^2 - (something). Test lam*Sum_nonedge g^2 = lam(n-lam)
        cand = lam * q['sum_g2_ne']    # = lam(n-lam)
        # candidate B: covariance-like. Just report gap vs simple nonedge aggregates
        avg = gap / len(ne)
        print(f"  {nm:12s} gap={gap:9.4f}  λ(n-λ)={cand:9.4f}  gap/#ne={avg:8.4f}  "
              f"min g²_ne={min((f[i]-f[j])**2 for i,j in ne):.4f}")

    print("\n" + "=" * 92)
    print("TASK 6 — is the bracket λ(2fDf-λ-S²/m-(n-2)) a clean nonedge sum? use Σmdeg f²=Σnonedge(f²+f²)")
    print("=" * 92)
    # bracket = lam*(n - 2*Sum_v mdeg_v f_v^2 - lam - S^2/m); and 2 Sum mdeg f^2 = 2 Sum_nonedge (f_i^2+f_j^2)
    for nm, q in data:
        n, lam, f, m, S, A, d = q['n'], q['lam'], q['f'], q['m'], q['S'], q['A'], q['d']
        mdeg = (n - 1) - d
        sm = float(np.sum(mdeg * f * f))               # Sum_v mdeg_v f_v^2
        # verify 2*sm = 2*Sum_nonedge(f_i^2+f_j^2)
        chk = sum(f[i] ** 2 + f[j] ** 2 for i, j in q['nonedges'])
        bracket = lam * (n - 2 * sm - lam - S ** 2 / m)
        bracket0 = lam * (2 * q['fDf'] - lam - S ** 2 / m - (n - 2))
        print(f"  {nm:12s} Σmdeg·f²={sm:.4f} (=Σ_ne(f²+f²)={chk:.4f}? {abs(sm-chk)<1e-6}) "
              f"bracket={bracket:.4f}(={bracket0:.4f}? {abs(bracket-bracket0)<1e-6})")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print("  complement eigvec Sum_nonedge g²=n-λ EXACT; T=(n-2)λ-Σdef·g² EXACT; gap=bracket+Σdef·g².")
    print("  Test whether gap is a sign-definite per-nonedge sum or stays mixed.")


if __name__ == "__main__":
    main()
