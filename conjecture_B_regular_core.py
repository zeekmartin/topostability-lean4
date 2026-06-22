"""
Regular-core inequality. For d-regular connected G (S=0):
  gap = λ(n-λ) - C,  C = Σ_{G-edge ab} tbar_ab (f_a-f_b)²,  tbar_ab = #common NON-neighbors.
Target: C <= λ(n-λ).  (Derived: Σdef·g² - λΣ_ne h² = λ(n-λ) - C for regular.)
Run: python conjecture_B_regular_core.py
"""
import numpy as np
import networkx as nx


def analyze(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f)
    regular = (d.max() == d.min())
    Abar = (np.ones((n, n)) - np.eye(n)) - A
    Abar2 = Abar @ Abar
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    C = sum(Abar2[i, j] * (f[i] - f[j]) ** 2 for (i, j) in edges)   # tbar weighted
    # true gap
    A2 = A @ A
    T = sum(A2[i, j] * (f[i] - f[j]) ** 2 for (i, j) in edges)
    gap = lam * (2 * float(d @ (f * f)) - lam - S ** 2 / m) - T
    return dict(n=n, d=float(d[0]) if regular else -1, regular=regular, lam=lam, C=C, gap=gap,
                lamnlam=lam * (n - lam), ratio=C / (lam * (n - lam)) if lam * (n - lam) > 1e-9 else 0.0,
                ev=ev, f=f, A=A, idx=idx)


def regular_corpus():
    out = []
    out.append(("rr20_4", nx.random_regular_graph(4, 20, seed=1)))
    out.append(("rr20_6", nx.random_regular_graph(6, 20, seed=2)))
    out.append(("rr30_10", nx.random_regular_graph(10, 30, seed=1)))
    out.append(("rr40_20", nx.random_regular_graph(20, 40, seed=1)))
    out.append(("cycle20", nx.cycle_graph(20)))
    out.append(("cycle7", nx.cycle_graph(7)))
    out.append(("petersen", nx.petersen_graph()))
    out.append(("paley13", nx.Graph(nx.paley_graph(13)) if hasattr(nx, 'paley_graph') else None))
    out.append(("hypercube4", nx.hypercube_graph(4)))
    out.append(("complete_bip_55", nx.complete_bipartite_graph(5, 5)))
    out.append(("complete_bip_77", nx.complete_bipartite_graph(7, 7)))
    out.append(("complete_mult_333", nx.complete_multipartite_graph(3, 3, 3)))
    out.append(("complete_mult_444", nx.complete_multipartite_graph(4, 4, 4)))
    out.append(("cocktail_5", nx.complete_multipartite_graph(*([2] * 5))))  # K_{2,2,2,2,2}
    out.append(("circ_ladder10", nx.circular_ladder_graph(10)))
    out.append(("K20", nx.complete_graph(20)))
    return [(nm, G) for nm, G in out if G is not None and nx.is_connected(G)]


def main():
    print("=" * 96)
    print("TASK 1/3 — regular reduction: gap = λ(n-λ) - C ; target C <= λ(n-λ). Verify & ratio C/λ(n-λ)")
    print("=" * 96)
    print(f"  {'graph':18s} {'n':>4} {'d':>4} {'λ':>8} {'C':>9} {'λ(n-λ)':>9} {'gap':>9} "
          f"{'λ(n-λ)-C':>9} {'C/λ(n-λ)':>9}")
    eqcases = []
    for nm, G in regular_corpus():
        q = analyze(G)
        match = abs((q['lamnlam'] - q['C']) - q['gap']) < 1e-6
        flag = "  <-EQ" if q['gap'] < 1e-6 else ""
        if q['gap'] < 1e-6: eqcases.append(nm)
        print(f"  {nm:18s} {q['n']:4d} {int(q['d']):4d} {q['lam']:8.4f} {q['C']:9.4f} "
              f"{q['lamnlam']:9.4f} {q['gap']:9.4f} {q['lamnlam']-q['C']:9.4f} {q['ratio']:9.4f}"
              f"{flag} {'OK' if match else 'BAD'}")
    print(f"\n  gap = λ(n-λ) - C verified; equality (gap≈0) cases: {eqcases}")

    print("\n" + "=" * 96)
    print("TASK 4 — equality analysis: which regular graphs saturate C = λ(n-λ)?")
    print("=" * 96)
    print("  K_n: λ=n => λ(n-λ)=0, C=0 (no non-edges) => equality.")
    print("  complete multipartite K_{a,...,a}: check if C = λ(n-λ) (gap=0)?")
    for nm, G in regular_corpus():
        if 'complete' in nm or 'cocktail' in nm or nm == 'K20':
            q = analyze(G)
            print(f"    {nm:18s} gap={q['gap']:.5f} ratio C/λ(n-λ)={q['ratio']:.4f} "
                  f"{'EQUALITY' if q['gap']<1e-6 else 'strict'}")

    print("\n" + "=" * 96)
    print("TASK 2 — quadratic-form view: C = Σ_G-edge (A_Ḡ²)_ab g_ab² ; λ(n-λ)=(fᵀL_Gf)(fᵀL_Ḡf)")
    print("=" * 96)
    print("  test candidate bound: C <= λ_max-related? Compare C to (n-λ)·(per-edge max tbar)·λ etc.")
    for nm, G in [("rr20_6", None), ("petersen", None), ("complete_bip_77", None), ("cycle20", None)]:
        G = dict(regular_corpus())[nm]
        q = analyze(G); n, lam = q['n'], q['lam']
        # tbar max over edges
        Abar2 = ((np.ones((n, n)) - np.eye(n)) - q['A']); Abar2 = Abar2 @ Abar2
        edges = [(i, j) for i in range(n) for j in range(i + 1, n) if q['A'][i, j] > 0]
        tbar_max = max(Abar2[i, j] for i, j in edges) if edges else 0
        # C <= tbar_max * Σ_edge g² = tbar_max * λ
        print(f"    {nm:18s} C={q['C']:.4f}  tbar_max·λ={tbar_max*lam:.4f}  λ(n-λ)={q['lamnlam']:.4f}  "
              f"(C<=tbar_max·λ? {q['C']<=tbar_max*lam+1e-9}; tbar_max·λ<=λ(n-λ)? {tbar_max*lam<=q['lamnlam']+1e-9})")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print("  Regular: gap = λ(n-λ) - C, C=Σtbar·g². Target C<=λ(n-λ). Equality cases & bound structure.")


if __name__ == "__main__":
    main()
