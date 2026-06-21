"""
Edge-deletion monotonicity of R = T/(lam2 G). Does K_n maximize R (R(K_n)=1)?

R = T/(lam2*Gvar), T=sum_e t_e g_e^2 (unordered), Gvar=sum_e h_e^2 - S^2/m, lam2=fiedler eig.
Tasks: (1) single-edge from K_n n=5..100; (2) deletion sequences; (3) monotone non-increasing?;
(4) counterexamples; (5) first-order deletion formula at K_n.
Run: python conjecture_B_R_edge_deletion.py
"""
import numpy as np
import networkx as nx


def R_of(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); A2 = A @ A
    T = sum(A2[idx[u], idx[v]] * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    Gvar = Gsum - S ** 2 / m; lam2G = lam * Gvar
    return dict(n=n, lam=lam, T=T, Gvar=Gvar, lam2G=lam2G, R=T / lam2G if lam2G > 1e-12 else float('nan'))


def main():
    print("=" * 80)
    print("TASK 1 — single-edge deletion from K_n (edge-transitive => one value per n)")
    print("=" * 80)
    print(f"  {'n':>4} {'R(K_n)':>8} {'R(K_n-e)':>10} {'lam2(K_n-e)':>12} {'<=1?':>6} {'<=R(K_n)?':>10}")
    for n in [5, 8, 12, 20, 40, 70, 100]:
        Rk = R_of(nx.complete_graph(n))
        Ge = nx.complete_graph(n); Ge.remove_edge(0, 1); Re = R_of(Ge)
        print(f"  {n:4d} {Rk['R']:8.5f} {Re['R']:10.5f} {Re['lam']:12.4f} "
              f"{str(Re['R']<=1+1e-9):>6} {str(Re['R']<=Rk['R']+1e-9):>10}")
    print("  (R(K_n)=1; deleting one edge => Fiedler localizes on e, lam2=n-2; is R<=1 still?)")

    print("\n" + "=" * 80)
    print("TASK 2/3 — deletion sequences from K_n: is R monotone non-increasing? max stays at K_n?")
    print("=" * 80)
    rng = np.random.default_rng(0)
    for n in [20, 40]:
        G = nx.complete_graph(n); Rs = [R_of(G)['R']]
        edges = list(G.edges()); rng.shuffle(edges)
        kept = 0
        for e in edges:
            if G.degree(e[0]) <= 2 or G.degree(e[1]) <= 2: continue
            G.remove_edge(*e)
            r = R_of(G)
            if r is None: G.add_edge(*e); continue
            Rs.append(r['R']); kept += 1
            if kept >= int(0.6 * len(edges)): break
        Rs = np.array(Rs)
        inc = int((np.diff(Rs) > 1e-9).sum())
        print(f"  n={n}: {len(Rs)} states; R start={Rs[0]:.4f} max={Rs.max():.4f} min={Rs.min():.4f}; "
              f"steps with R increase: {inc}/{len(Rs)-1}; max<=R(K_n)+eps: {Rs.max()<=Rs[0]+1e-6}")

    print("\n" + "=" * 80)
    print("TASK 4 — does ANY graph have R > 1 (=> K_n not global max)? broad search")
    print("=" * 80)
    worst = 0.0; worstg = None; cnt = 0
    for n in [10, 15, 20, 30]:
        for q in np.linspace(0.2, 0.95, 8):
            for s in range(3):
                H = nx.gnp_random_graph(n, float(q), seed=int(rng.integers(1e9)))
                r = R_of(H)
                if r is None: continue
                cnt += 1
                if r['R'] > worst: worst = r['R']; worstg = (n, round(float(q), 2))
        # near-complete: K_n minus k edges
        for k in [1, 2, 3, 5]:
            G = nx.complete_graph(n); ed = list(G.edges()); rng.shuffle(ed)
            for e in ed[:k]:
                if G.degree(e[0]) > 2 and G.degree(e[1]) > 2: G.remove_edge(*e)
            r = R_of(G)
            if r and r['R'] > worst: worst = r['R']; worstg = (n, f"K-{k}")
    print(f"  tested {cnt} random + near-complete graphs; max R found = {worst:.5f} at {worstg}")
    print(f"  R > 1 anywhere? {worst > 1 + 1e-6}  (if NO: K_n (R=1) is the global max)")

    print("\n" + "=" * 80)
    print("TASK 5 — first-order at K_n: R(K_n-e), DeltaT, Delta(lam2G), DeltaR (exact small-n)")
    print("=" * 80)
    print(f"  {'n':>4} {'R(K_n)':>8} {'R(K_n-e)':>10} {'DeltaR':>10} {'T(K_n)':>9} {'T(K-e)':>9} "
          f"{'lam2G(K)':>9} {'lam2G(K-e)':>11}")
    for n in [5, 8, 12, 20, 40]:
        Rk = R_of(nx.complete_graph(n))
        Ge = nx.complete_graph(n); Ge.remove_edge(0, 1); Re = R_of(Ge)
        print(f"  {n:4d} {Rk['R']:8.5f} {Re['R']:10.5f} {Re['R']-Rk['R']:10.5f} "
              f"{Rk['T']:9.3f} {Re['T']:9.3f} {Rk['lam2G']:9.3f} {Re['lam2G']:11.3f}")
    # the localized-Fiedler closed form for K_n - e
    print("\n  closed form (K_n - e, Fiedler f=(e_i-e_j)/sqrt2, lam2=n-2):")
    for n in [10, 20, 40]:
        # T = 2*(n-3)*(n-2)*(1/2) [edges i-k and j-k, k!=i,j], unordered; Gvar, etc.
        Ge = nx.complete_graph(n); Ge.remove_edge(0, 1); Re = R_of(Ge)
        # predicted: f localized; T_unord = (n-2)*(n-3)*(1/2) per side *2 sides... verify vs actual
        print(f"    n={n}: actual R(K_n-e)={Re['R']:.5f}  lam2={Re['lam']:.1f}(=n-2={n-2})  "
              f"T={Re['T']:.3f}  Gvar={Re['Gvar']:.3f}")

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print("  Report: R(K_n-e) vs 1; monotone?; global max = K_n?; first-order DeltaR at K_n.")


if __name__ == "__main__":
    main()
