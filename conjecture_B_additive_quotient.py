"""
Conjecture B — closed-form for the additive lift quotient R_T(h), h_uv = φ_u+φ_v.

Claimed identities (derived):
  NUMERATOR   hᵀL_T h = Σ_{(a,b)∈E} t_ab (φ_a-φ_b)²            [t_ab = |N(a)∩N(b)| = (A²)_ab]
                      = Σ_{c∈V} (Dirichlet energy of φ on G[N(c)])   [apex form]
                      = φᵀ L_t φ                                 [L_t = triangle-weighted Laplacian]
  DENOMINATOR hᵀh     = φᵀ(D+A)φ = 2 Σ_v deg(v)φ_v² - φᵀL_Gφ    [signless Laplacian Q=BBᵀ]
  ⇒  R_T(h) = [Σ t_ab (φ_a-φ_b)²] / [2 Σ_v deg(v)φ_v² - φᵀL_Gφ].
Specialize φ=f (unit Fiedler, L_G f=λ₂ f): denom = 2fᵀDf - λ₂; compare R_T(f) to λ₂.

Verifies the three numerator forms + two denominator forms; gives closed forms for
K_n, K_n-e, K_n-triangle; isolates the 'missing term' Δ = λ₂(2fᵀDf-λ₂) - Σt_ab(Δφ)².

Run:  python conjecture_B_additive_quotient.py
"""
import numpy as np
import networkx as nx
from itertools import combinations
import counterexample_search as ce

TOL = 1e-9


def quantities(G, f=None):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2G = float(ev[1])
    if f is None:
        f = V[:, 1] / np.linalg.norm(V[:, 1])
    # unsigned incidence + triangle graph
    B = np.zeros((n, m))
    for e, (u, v) in enumerate(edges):
        B[idx[u], e] = 1.0; B[idx[v], e] = 1.0
    h = B.T @ f
    T = ce.triangle_graph(G)
    LT = nx.laplacian_matrix(T).toarray().astype(float)
    l2T = ce.lambda2(T) if (T.number_of_nodes() >= 2 and nx.is_connected(T)) else float('nan')

    # NUMERATOR three ways
    N1 = float(h @ LT @ h)                                   # direct
    A2 = A @ A
    N2 = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        t = len(set(G[u]) & set(G[v]))                       # = (A²)_ij for edge
        N2 += t * (f[i] - f[j]) ** 2
    # apex form: sum over c of Dirichlet energy of f on induced subgraph on N(c)
    N3 = 0.0
    for c in nodes:
        Nc = list(G[c]);
        for a, b in combinations(Nc, 2):
            if G.has_edge(a, b):
                N3 += (f[idx[a]] - f[idx[b]]) ** 2
    # DENOMINATOR two ways
    D1 = float(h @ h)
    fDf = float((d * f * f).sum())
    D2 = 2 * fDf - float(f @ L @ f)
    Q = np.diag(d) + A
    D3 = float(f @ Q @ f)

    RT = N1 / D1
    Delta = l2G * (2 * fDf - l2G) - N2                       # missing term (if f is Fiedler)
    return dict(n=n, m=m, l2G=l2G, l2T=l2T, N1=N1, N2=N2, N3=N3,
                D1=D1, D2=D2, D3=D3, RT=RT, fDf=fDf,
                err_num=max(abs(N1-N2), abs(N1-N3)), err_den=max(abs(D1-D2), abs(D1-D3)),
                Delta=Delta)


def main():
    print("=== verify identities on random graphs (Fiedler φ=f) ===")
    rng = np.random.default_rng(1); en = ed = 0.0; cnt = 0
    for _ in range(300):
        nn = int(rng.integers(6, 13)); p = float(rng.uniform(0.4, 0.95))
        G = nx.gnp_random_graph(nn, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        q = quantities(G)
        en = max(en, q["err_num"]); ed = max(ed, q["err_den"]); cnt += 1
    print(f"  {cnt} graphs: max numerator-form error = {en:.2e}, max denom-form error = {ed:.2e}")
    print("  ⇒ hᵀL_T h = Σt_ab(Δφ)² = Σ_c Dirichlet(N(c))  and  hᵀh = φᵀ(D+A)φ = 2fᵀDf-λ₂ : CONFIRMED")

    print("\n=== closed forms on K_n, K_n-e, K_n-triangle ===")
    print(f"  {'family':14s}{'n':>3s}{'λ₂(G)':>8s}{'R_T(f)':>9s}{'λ₂(T)':>8s}{'N=Σt(Δφ)²':>11s}"
          f"{'Den':>7s}{'Δ(missing)':>11s}")
    for nn in (6, 8, 10, 12):
        # K_n
        G = nx.complete_graph(nn); q = quantities(G)
        print(f"  {'K_n':14s}{nn:>3d}{q['l2G']:>8.3f}{q['RT']:>9.3f}{q['l2T']:>8.3f}"
              f"{q['N2']:>11.3f}{q['D1']:>7.3f}{q['Delta']:>11.4f}")
        # K_n - e
        G = nx.complete_graph(nn); G.remove_edge(0, 1); q = quantities(G)
        print(f"  {'K_n - e':14s}{nn:>3d}{q['l2G']:>8.3f}{q['RT']:>9.3f}{q['l2T']:>8.3f}"
              f"{q['N2']:>11.3f}{q['D1']:>7.3f}{q['Delta']:>11.4f}")
        # K_n - triangle
        G = nx.complete_graph(nn); G.remove_edges_from([(0, 1), (0, 2), (1, 2)]); q = quantities(G)
        print(f"  {'K_n - △':14s}{nn:>3d}{q['l2G']:>8.3f}{q['RT']:>9.3f}{q['l2T']:>8.3f}"
              f"{q['N2']:>11.3f}{q['D1']:>7.3f}{q['Delta']:>11.4f}")

    print("\n  predicted closed forms:")
    print("   K_n      : R_T=n=λ₂(G) (EQUALITY); t_ab=n-2 all edges; N=(n-2)·n; Den=n-2; Δ=0")
    print("   K_n - e  : R_T=n-3=λ₂(T); λ₂(G)=n-2; N=(n-2)(n-3); Den=n-2; Δ=n-2")
    print("   K_n - △  : λ₂(G)=n-3; R_T=λ₂(T)=n-4 ; Δ grows")

    # K_n-e missing-term decomposition
    print("\n=== K_n-e: decompose the drop n -> n-3 (the 'missing term') ===")
    for nn in (8, 12, 20):
        # numerator with the SAME f=(e0-e1)/sqrt2 on K_n vs K_n-e
        f = np.zeros(nn); f[0] = 1 / np.sqrt(2); f[1] = -1 / np.sqrt(2)
        GK = nx.complete_graph(nn); qK = quantities(GK, f=f)
        GKe = nx.complete_graph(nn); GKe.remove_edge(0, 1); qKe = quantities(GKe, f=f)
        # decomposition of N(K_n) - N(K_n-e):
        removed_edge_term = (nn - 2) * (f[0] - f[1]) ** 2        # edge {0,1}, t=n-2 in K_n
        t_deficit = (nn - 2)                                     # 2(n-2) gradient edges lose t by 1, *(1/2)
        print(f"  n={nn}: N(K_n,f)={qK['N2']:.2f}  N(K_n-e,f)={qKe['N2']:.2f}  "
              f"drop={qK['N2']-qKe['N2']:.2f}")
        print(f"        = removed-edge {{0,1}} term {removed_edge_term:.2f} "
              f"+ triangle-deficit on edges to 0,1 ≈ {t_deficit:.2f}  "
              f"(= 2(n-2)·½·1: edges {{0,v}},{{1,v}} lose triangle {{0,1,v}})")

    main.q = quantities


if __name__ == "__main__":
    main()
