"""
Conjecture B — global/variational search from the EXACT inequality.
B(f): Σ_{ab∈E} t_ab (f_a-f_b)² ≤ λ₂(G)·fᵀ(D+A)f, f=unit Fiedler. L_t = triangle-
weighted Laplacian (weight t_ab=(A²)_ab on edge ab), Q=D+A. Δ = λ₂ fᵀQf - fᵀL_t f.

TASK 0: operator test — is λ₂(G)·Q - L_t PSD on 1⊥ (i.e. for ALL x⊥1)?
        = smallest eigenvalue of Zᵀ(λ₂Q-L_t)Z, Z = basis of 1⊥.  Report min over corpus.
TASK 3: full spectrum of (λ₂Q-L_t)|_{1⊥} for K_n, K_n-e, K_n-△, Petersen.
LEMMA 4: edge-monotonicity  w_uv = Δ(G) - Δ(G+uv) ≥ 0 ?  (⇒ B by induction from K_n)
LEMMA 3: eigenvector expansion of fᵀ(A∘A²)f using Af=(D-λ₂)f.

Run:  python conjecture_B_global_variational.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def ops(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; Q = np.diag(d) + A
    A2 = A @ A
    Wt = A * A2                              # Hadamard A∘A² : weight t_ab on edges
    Lt = np.diag(Wt.sum(1)) - Wt             # triangle-weighted Laplacian
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    return nodes, idx, n, L, d, A, Q, Lt, l2, f, ev


def Z_perp1(n):
    M = np.eye(n) - np.ones((n, n)) / n
    U, s, _ = np.linalg.svd(M)
    return U[:, s > 1e-9]                     # n x (n-1), orthonormal basis of 1⊥


def op_min_eig(G):
    """smallest eigenvalue of (λ₂Q - L_t) restricted to 1⊥."""
    nodes, idx, n, L, d, A, Q, Lt, l2, f, ev = ops(G)
    Z = Z_perp1(n)
    Mdiff = Z.T @ (l2 * Q - Lt) @ Z
    w = np.linalg.eigvalsh(0.5 * (Mdiff + Mdiff.T))
    return float(w[0]), l2


def Delta(G):
    """Δ(G) = λ₂ fᵀQf - fᵀL_t f, f=Fiedler. (B(f) ⟺ Δ≥0.)"""
    nodes, idx, n, L, d, A, Q, Lt, l2, f, ev = ops(G)
    return float(l2 * (f @ Q @ f) - f @ Lt @ f)


def corpus(maxn=9):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def main():
    print("=== TASK 0: operator inequality  λ₂Q - L_t ⪰ 0 on 1⊥ ? ===")
    graphs = corpus(9)
    worst = (1e9, None); npos = 0; N = 0
    for G in graphs:
        me, l2 = op_min_eig(G)
        N += 1
        if me >= -1e-7:
            npos += 1
        if me < worst[0]:
            worst = (me, (G.number_of_nodes(), G.number_of_edges()))
    print(f"  {N} distinct graphs; operator-PSD-on-1⊥ holds: {npos}/{N} ({100*npos/N:.1f}%)")
    print(f"  MIN smallest-eig of (λ₂Q-L_t)|_1⊥ across corpus = {worst[0]:+.4f} at n,m={worst[1]}")
    if worst[0] < -1e-7:
        print("  ⇒ operator inequality FAILS: B REQUIRES the eigenvector constraint L_G f=λ₂f.")
    else:
        print("  ⇒ operator inequality HOLDS: B follows from operator domination alone!")

    print("\n=== TASK 3: spectrum of (λ₂Q - L_t)|_1⊥ for named graphs ===")
    named = [("K_8", nx.complete_graph(8)),
             ("K_8-e", _rm(nx.complete_graph(8), [(0, 1)])),
             ("K_8-△", _rm(nx.complete_graph(8), [(0, 1), (0, 2), (1, 2)])),
             ("Petersen", nx.petersen_graph())]
    for name, G in named:
        nodes, idx, n, L, d, A, Q, Lt, l2, f, ev = ops(G)
        Z = Z_perp1(n)
        spec = np.linalg.eigvalsh(0.5 * (Z.T @ (l2 * Q - Lt) @ Z + (Z.T @ (l2 * Q - Lt) @ Z).T))
        print(f"  {name:9s} λ₂={l2:.3f}  Δ={Delta(G):+.3f}  spec(λ₂Q-Lt|1⊥): "
              f"min={spec.min():+.3f} max={spec.max():+.3f}  #neg={int(np.sum(spec<-1e-7))}/{len(spec)}")

    print("\n=== LEMMA 4: edge-monotonicity  w_uv = Δ(G) - Δ(G+uv) ≥ 0 ? ===")
    # sample of corpus + hard families
    import random
    sample = graphs[:400]
    rng = np.random.default_rng(1)
    # add hard families
    for _ in range(40):
        nn = int(rng.integers(16, 26)); q = float(rng.uniform(0.55, 0.72))
        Gb = nx.gnp_random_graph(nn - 1, q, seed=int(rng.integers(0, 2**31)))
        Gb = nx.relabel_nodes(Gb, {i: i + 1 for i in range(nn - 1)}); Gb.add_node(0)
        for b in rng.choice(range(1, nn), size=2, replace=False):
            Gb.add_edge(0, int(b))
        if nx.is_connected(Gb):
            sample.append(Gb)
    sample.append(nx.petersen_graph())
    wmin = (1e9, None); ntot = 0; nviol = 0; ngraph = 0; npart = 0
    for G in sample:
        if not nx.is_connected(G):
            continue
        n = G.number_of_nodes()
        dG = Delta(G); ngraph += 1
        nonedges = list(nx.non_edges(G))
        if not nonedges:
            continue
        sumw = 0.0; gbad = False
        for (u, v) in nonedges:
            H = G.copy(); H.add_edge(u, v)
            if not nx.is_connected(H):
                continue
            w = dG - Delta(H)
            sumw += w; ntot += 1
            if w < -1e-7:
                nviol += 1; gbad = True
            if w < wmin[0]:
                wmin = (w, (n, G.number_of_edges()))
        # is Σ w_uv ≈ Δ(G)? (would need Δ at the 'all-non-edges-added'=K_n end; partial check)
        if abs(sumw - dG) < 1e-6 * max(abs(dG), 1):
            npart += 1
    print(f"  tested {ntot} non-edge additions over {ngraph} graphs")
    print(f"  w_uv < 0 (Δ INCREASES when adding edge): {nviol} ({100*nviol/max(ntot,1):.2f}%)")
    print(f"  MIN w_uv = {wmin[0]:+.4f} at n,m={wmin[1]}")
    if nviol == 0:
        print("  ⇒ Δ is MONOTONE non-increasing under edge addition ⇒ B by induction from K_n!")
    else:
        print("  ⇒ Δ is NOT monotone in edges; induction-from-K_n via single-edge steps fails.")

    print("\n=== LEMMA 3: eigenvector expansion fᵀ(A∘A²)f vs Af=(D-λ₂)f ===")
    for name, G in [("K_8-e", named[1][1]), ("Petersen", nx.petersen_graph()),
                    ("gnp10", nx.gnp_random_graph(10, 0.6, seed=2))]:
        nodes, idx, n, L, d, A, Q, Lt, l2, f, ev = ops(G)
        A2 = A @ A
        lhs = float(f @ (A * A2) @ f)            # fᵀ(A∘A²)f = Σ_ab t_ab f_a f_b *2? (sym)
        # compare to fᵀ A³ f / fᵀA f etc (A³ counts closed walks)
        fA3f = float(f @ (A @ A @ A) @ f)
        fAf = float(f @ A @ f)
        print(f"  {name:9s}: fᵀ(A∘A²)f={lhs:.4f}  fᵀA³f={fA3f:.4f}  fᵀAf={fAf:.4f}  "
              f"fᵀDf-λ₂={float((d*f*f).sum())-l2:.4f}")

    main.graphs = graphs


def _rm(G, es):
    G.remove_edges_from(es); return G


if __name__ == "__main__":
    main()
