"""
Conjecture B — quantify the additivity mechanism.

ψ = unit T(G)-Fiedler vector (L_T ψ = λ₂(T) ψ, ψ⊥1_E).
U_d = range(Bᵀ|_{d⊥}) (additive subspace, ⊥1_E).  ψ_add = P_{U_d} ψ, ψ_perp = ψ-ψ_add.
α = ‖ψ_add‖²/‖ψ‖²  (=1 ⇔ K_n).   ratio = λ₂(T)/λ₂(G) (≤1).

Tests on all DISTINCT corpus graphs (deduped):
  (T1) ratio ≤ α    [if true & α≤1 always ⇒ B; candidate proof reduction]
  (T2) R_T(ψ_add) = ψ_addᵀL_Tψ_add/‖ψ_add‖² ≤ λ₂(G)   [the user's crux]
  (T3) μ(G)=min Ritz on U_d ≤ λ₂(G)  [known, 100%]
Plus: relationship ratio=f(α); α for K_n-e (does 1-α ~ c/n?).

Run:  python conjecture_B_additivity_proof.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def analyse(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    ev, _ = np.linalg.eigh(L); l2G = float(ev[1])
    if l2G <= 1e-7:
        return None
    T = ce.triangle_graph(G)
    if T.number_of_nodes() < 2 or not nx.is_connected(T):
        return None
    LT = nx.laplacian_matrix(T).toarray().astype(float)
    evT, VT = np.linalg.eigh(LT); l2T = float(evT[1])
    if l2T <= 1e-7:
        return None
    psi = VT[:, 1] / np.linalg.norm(VT[:, 1])
    mult = int(np.sum(np.abs(evT - l2T) < 1e-7))
    # additive subspace U_d
    B = np.zeros((n, m))
    for e, (u, v) in enumerate(edges):
        B[idx[u], e] = 1.0; B[idx[v], e] = 1.0
    dv = d / np.linalg.norm(d)
    Usv, s, _ = np.linalg.svd(np.eye(n) - np.outer(dv, dv))
    P = Usv[:, s > 1e-9]                      # n x (n-1), cols ⊥ d
    Qb, _ = np.linalg.qr(B.T @ P)             # orthonormal basis of U_d (m x (n-1))
    coeff = Qb.T @ psi
    alpha = float(coeff @ coeff)              # ‖ψ_add‖² (ψ unit)
    psi_add = Qb @ coeff
    na = float(psi_add @ psi_add)
    RT_add = float(psi_add @ LT @ psi_add) / na if na > 1e-12 else float("inf")
    comp = Qb.T @ LT @ Qb
    mu = float(np.linalg.eigvalsh(0.5 * (comp + comp.T))[0])
    return dict(n=n, m=m, l2G=l2G, l2T=l2T, ratio=l2T / l2G, alpha=alpha,
                RT_add=RT_add, mu=mu, mult=mult,
                complete=(m == n * (n - 1) // 2))


def corpus_distinct():
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(9):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def main():
    graphs = corpus_distinct()
    rows = []
    for G in graphs:
        r = analyse(G)
        if r is not None:
            rows.append(r)
    N = len(rows)
    print(f"distinct corpus graphs with T(G) connected: {N}")

    a = np.array([r["alpha"] for r in rows])
    ratio = np.array([r["ratio"] for r in rows])
    rt_add = np.array([r["RT_add"] / r["l2G"] for r in rows])
    mu = np.array([r["mu"] / r["l2G"] for r in rows])
    simple = [r for r in rows if r["mult"] == 1]   # well-defined ψ

    print(f"\n[α] additivity fraction ‖ψ_add‖²:")
    print(f"   min={a.min():.4f}  median={np.median(a):.4f}  max={a.max():.4f}")
    print(f"   #graphs with α>0.999 (≈fully additive): {int(np.sum(a>0.999))} "
          f"(complete: {sum(1 for r in rows if r['complete'])})")
    print(f"   #graphs with λ₂(T) simple (ψ well-defined): {len(simple)}/{N}")

    print(f"\n[T1] ratio = λ₂(T)/λ₂(G) ≤ α ?   (if always true ⇒ B, since α≤1)")
    t1 = np.mean(ratio <= a + 1e-9)
    t1s = np.mean([r["ratio"] <= r["alpha"] + 1e-9 for r in simple])
    margin = (a - ratio)
    print(f"   holds: {100*t1:.2f}% (all)  {100*t1s:.2f}% (simple-λ₂(T))")
    print(f"   margin (α - ratio): min={margin.min():+.4f}  median={np.median(margin):.4f}")
    if (ratio > a + 1e-7).any():
        bad = [r for r in rows if r["ratio"] > r["alpha"] + 1e-7]
        bad.sort(key=lambda r: r["ratio"] - r["alpha"], reverse=True)
        print(f"   VIOLATIONS of ratio≤α: {len(bad)}; worst:")
        for r in bad[:5]:
            print(f"     n={r['n']} m={r['m']} ratio={r['ratio']:.4f} α={r['alpha']:.4f} "
                  f"mult={r['mult']} complete={r['complete']}")

    print(f"\n[T2] R_T(ψ_add) ≤ λ₂(G) ?   (the proof crux)")
    t2 = np.mean(rt_add <= 1 + 1e-9)
    t2s = np.mean([r["RT_add"] <= r["l2G"] + 1e-9 for r in simple])
    print(f"   holds: {100*t2:.2f}% (all)  {100*t2s:.2f}% (simple-λ₂(T))")
    print(f"   R_T(ψ_add)/λ₂(G): median={np.median(rt_add):.4f}  max={rt_add.max():.4f}")
    if (rt_add > 1 + 1e-7).any():
        bad = [r for r in rows if r["RT_add"] > r["l2G"] + 1e-7]
        bad.sort(key=lambda r: r["RT_add"] / r["l2G"], reverse=True)
        print(f"   VIOLATIONS of R_T(ψ_add)≤λ₂(G): {len(bad)}; worst:")
        for r in bad[:5]:
            print(f"     n={r['n']} m={r['m']} R_T(add)/λ₂(G)={r['RT_add']/r['l2G']:.4f} "
                  f"α={r['alpha']:.4f} ratio={r['ratio']:.4f} mult={r['mult']}")

    print(f"\n[T3] μ(G) ≤ λ₂(G) (known): {100*np.mean(mu<=1+1e-9):.2f}%  "
          f"median μ/λ₂(G)={np.median(mu):.4f}")

    # relationship ratio vs α (on simple-λ₂ graphs)
    rs = np.array([r["ratio"] for r in simple]); als = np.array([r["alpha"] for r in simple])
    if len(rs) > 2:
        cc = np.corrcoef(rs, als)[0, 1]
        print(f"\n[fit] corr(ratio, α) over simple-λ₂ graphs = {cc:+.4f}")
        # is ratio ≈ α? or ratio ≤ α with slack? report mean(ratio/α)
        print(f"      mean ratio/α = {np.mean(rs/als):.4f}  median = {np.median(rs/als):.4f}")

    # K_n - e family
    print(f"\n[K_n - e] does 1-α scale like 1/n (matching ratio=(n-3)/(n-2))?")
    print(f"   {'n':>3s}{'ratio':>9s}{'α':>9s}{'1-α':>9s}{'R_T(add)/λ₂':>13s}")
    for nn in (8, 10, 12, 16, 20, 26):
        G = nx.complete_graph(nn); G.remove_edge(0, 1)
        r = analyse(G)
        if r:
            print(f"   {nn:>3d}{r['ratio']:>9.4f}{r['alpha']:>9.4f}{1-r['alpha']:>9.4f}"
                  f"{r['RT_add']/r['l2G']:>13.4f}")

    main.rows = rows


if __name__ == "__main__":
    main()
