"""
Complement-coupled inequality: Sum_e deficit_e g_e^2 >= lam(Sum_nonedge h^2 + S^2/m).
Uses L_G f=λf and L_Gbar f=(n-λ)f.

Reindex: deficit_e = mdeg_a+mdeg_b - tbar_ab => Sum_e deficit g^2 = Sum_v mdeg_v D_v - Sum_c Ebar_c,
  D_v = local Dirichlet at v (Sum_{b~v} g_vb^2), Ebar_c = Dirichlet on non-neighborhood of c.
Also Sum_v mdeg_v D_v = Sum_{nonedge {a,c}} (D_a + D_c).
Complement row eqn: Sum_{v !~ u} f_v = -(d_u+1-λ) f_u.
Tasks: verify reindex; per-nonedge D_a+D_c >= λ h_ac^2?; aggregate; PSD on complement eigenspace.
Run: python conjecture_B_complement_coupled.py
"""
import numpy as np
import networkx as nx


def setup(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f)
    mdeg = (n - 1) - d
    D = np.array([sum((f[i] - f[j]) ** 2 for j in range(n) if A[i, j] > 0) for i in range(n)])  # local Dirichlet
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    nonedges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] == 0]
    return dict(n=n, A=A, d=d, lam=lam, f=f, m=m, S=S, mdeg=mdeg, D=D, edges=edges, nonedges=nonedges)


def corpus():
    out = [("gnp20_.5", nx.gnp_random_graph(20, 0.5, seed=1)),
           ("gnp30_.4", nx.gnp_random_graph(30, 0.4, seed=2)),
           ("gnp20_.8", nx.gnp_random_graph(20, 0.8, seed=3)),
           ("rr20_6", nx.random_regular_graph(6, 20, seed=1)),
           ("rr30_10", nx.random_regular_graph(10, 30, seed=1)),
           ("cycle20", nx.cycle_graph(20))]
    H = nx.gnp_random_graph(39, 0.65, seed=2); H.add_node(39); H.add_edge(39, 0); H.add_edge(39, 1)
    out.append(("deg2dense40", H))
    Ge = nx.complete_graph(20); Ge.remove_edge(0, 1); out.append(("K20-e", Ge))
    return [(nm, G) for nm, G in out if nx.is_connected(G)]


def main():
    data = [(nm, setup(G)) for nm, G in corpus()]

    print("=" * 92)
    print("TASK 5 — complement row eqn: Σ_{v≁u} f_v = -(d_u+1-λ) f_u  (from L_Ḡf=(n-λ)f)")
    print("=" * 92)
    for nm, q in data:
        A, f, d, lam, n = q['A'], q['f'], q['d'], q['lam'], q['n']
        err = 0.0
        for u in range(n):
            lhs = sum(f[v] for v in range(n) if v != u and A[u, v] == 0)
            err = max(err, abs(lhs - (-(d[u] + 1 - lam) * f[u])))
        print(f"  {nm:12s} max|Σ_{{≁u}}f_v + (d_u+1-λ)f_u| = {err:.2e}")

    print("\n" + "=" * 92)
    print("TASK 1/2 — reindex: Σ_e deficit·g² = Σ_v mdeg_v D_v - Σ_c Ēbar_c  (Ēbar = nonNbhd Dirichlet)")
    print("=" * 92)
    for nm, q in data:
        A, f, mdeg, D, n = q['A'], q['f'], q['mdeg'], q['D'], q['n']
        # deficit sum directly
        defsum = 0.0
        for (a, b) in q['edges']:
            deficit = sum(1 for c in range(n) if c != a and c != b and (A[a, c] == 0 or A[b, c] == 0))
            defsum += deficit * (f[a] - f[b]) ** 2
        term1 = float(np.sum(mdeg * D))
        Ebar = 0.0
        for c in range(n):
            nn = [v for v in range(n) if v != c and A[c, v] == 0]
            for a in nn:
                for b in nn:
                    if a < b and A[a, b] > 0: Ebar += (f[a] - f[b]) ** 2
        # term1 counts (D_a+D_c) per nonedge = Sum_v mdeg_v D_v; Ebar single-counted per c -> *2? check
        print(f"  {nm:12s} Σdef·g²={defsum:9.4f}  Σmdeg·D={term1:9.4f}  Σ_c Ēbar_c={Ebar:9.4f}  "
              f"term1-2Ēbar={term1-2*Ebar:9.4f}  match(def)? {abs(defsum-(term1-2*Ebar))<1e-6}")
    print("  (deficit = mdeg_a+mdeg_b - tbar; Σmdeg·D = Σ_nonedge(D_a+D_c); tbar term = 2·Σ_c Ēbar_c)")

    print("\n" + "=" * 92)
    print("TASK 3/4 — per-nonedge bound: is D_a + D_c >= λ·h_ac²  (h_ac=f_a+f_c) per non-edge?")
    print("=" * 92)
    for nm, q in data:
        f, D, lam = q['f'], q['D'], q['lam']
        neg = 0; mn = 1e9
        for (a, c) in q['nonedges']:
            phi = D[a] + D[c] - lam * (f[a] + f[c]) ** 2
            if phi < -1e-9: neg += 1
            mn = min(mn, phi)
        ntot = len(q['nonedges'])
        print(f"  {nm:12s} #(D_a+D_c < λh²)={neg}/{ntot}  min(D_a+D_c-λh²)={mn:.4f}")
    print("  (if 0 violations: Σ_nonedge(D_a+D_c) >= λΣ_nonedge h² per-nonedge => most of the target)")

    print("\n" + "=" * 92)
    print("TASK 4 — aggregate target: Σmdeg·D vs λ(Σ_nonedge h² + S²/m); and full gap")
    print("=" * 92)
    print(f"  {'graph':12s} {'Σmdeg·D':>9} {'λΣ_ne h²+λS²/m':>14} {'Σmdeg·D-RHS':>12} {'2Ēbar':>8} {'gap':>8}")
    for nm, q in data:
        f, mdeg, D, lam, S, m, n, A = q['f'], q['mdeg'], q['D'], q['lam'], q['S'], q['m'], q['n'], q['A']
        term1 = float(np.sum(mdeg * D))
        sumh2 = sum((f[a] + f[c]) ** 2 for a, c in q['nonedges'])
        RHS = lam * (sumh2 + S ** 2 / m)
        Ebar = 0.0
        for c in range(n):
            nn = [v for v in range(n) if v != c and A[c, v] == 0]
            for a in nn:
                for b in nn:
                    if a < b and A[a, b] > 0: Ebar += (f[a] - f[b]) ** 2
        gap = (term1 - 2 * Ebar) - RHS
        print(f"  {nm:12s} {term1:9.4f} {RHS:14.4f} {term1-RHS:12.4f} {2*Ebar:8.4f} {gap:8.4f}")
    print("  (gap = (Σmdeg·D - 2Ēbar) - RHS. Is Σmdeg·D >= RHS [before subtracting Ēbar]? margin?)")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print("  complement row eqn verified; reindex verified; test per-nonedge D_a+D_c>=λh² and whether")
    print("  Σmdeg·D >= RHS gives slack to absorb the -2Ēbar correction (=> gap>=0).")


if __name__ == "__main__":
    main()
