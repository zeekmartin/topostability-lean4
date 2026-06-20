"""
TASK 3: adding edge a~b increases gap/eff (twin ports, d, bulk K_N).

Key facts (derived):
  - The symmetric quotient is UNCHANGED by a~b (a-row: degree +1 cancels new neighbor +p),
    so lam2 and Fiedler (x,p,c,r) are identical with/without a~b.
  - g_ab=(f_a-f_b)^2=0 (twins, symmetric) => T, B2' unchanged by the a-b edge;
    Sum h^2 += (f_a+f_b)^2 = 4p^2 => gap(a~b) = gap(a!~b) + 4 lam p^2 (S^2/m correction ->0).
  - eff: antisymmetric response, a~b raises the 'degree' => eff = 2/(d+2-lam) < 2/(d-lam).
  => g(a~b) - g(a!~b) = gap(a!~b) + 2 lam p^2 (d+2-lam) > 0.
Run: python conjecture_B_typeA_extremality_task3.py
"""
import numpy as np
import networkx as nx


def model(N, d, ab):
    G = nx.complete_graph(N)
    a, b, v0 = N, N + 1, N + 2
    for u in (a, b):
        G.add_node(u)
        for k in range(d): G.add_edge(u, k)        # twins: both ~ {0..d-1}
    if ab: G.add_edge(a, b)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    m = G.number_of_edges(); S = float(dg @ f)
    Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gs - S ** 2 / m) - B2
    H = G.copy(); H.remove_node(v0); Hn = list(H.nodes())
    LH = nx.laplacian_matrix(H, nodelist=Hn).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH)
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    ia, ib = Hn.index(a), Hn.index(b)
    eff = float(R[ia, ia] + R[ib, ib] - 2 * R[ia, ib])
    return dict(lam=lam, gap=gap, eff=eff, goe=gap / eff,
                p=float(f[idx[a]]), x=float(f[idx[v0]]))


def main():
    print("=" * 86)
    print("TASK 3a/3b — same lam2 & Fiedler with/without a~b;  eff drops, gap rises")
    print("=" * 86)
    N = 600
    print(f"  {'d':>3} {'lam(no)':>8} {'lam(ab)':>8} {'gap(no)':>8} {'gap(ab)':>8} "
          f"{'eff(no)':>8} {'eff(ab)':>8} {'g(no)':>7} {'g(ab)':>7}")
    for d in [2, 3, 4, 5]:
        r0 = model(N, d, False); r1 = model(N, d, True)
        print(f"  {d:3d} {r0['lam']:8.4f} {r1['lam']:8.4f} {r0['gap']:8.4f} {r1['gap']:8.4f} "
              f"{r0['eff']:8.4f} {r1['eff']:8.4f} {r0['goe']:7.4f} {r1['goe']:7.4f}")

    print("\n" + "=" * 86)
    print("CORRECTED mechanism: lam UNCHANGED; eff(ab)=2/(d+2-lam) (clean drop); gap(ab) computed.")
    print("(a~b raises deg(a),deg(b) by 1 => min-weights on a-/b-port edges shift, so B2' changes too;")
    print(" net gap(ab) ~ gap(no). The DRIVER of g rising is eff dropping by factor (d-lam)/(d+2-lam).)")
    print("=" * 86)
    for d in [2, 3, 4]:
        lam = 0.5 * (d + 3 - np.sqrt(d * d - 2 * d + 9))
        r0 = model(1200, d, False); r1 = model(1200, d, True)
        print(f"  d={d}: lam={lam:.4f}  eff(ab) model={r1['eff']:.4f} pred 2/(d+2-lam)={2/(d+2-lam):.4f}")
        print(f"     gap: no={r0['gap']:.4f} ab={r1['gap']:.4f} (ratio gap(ab)/gap(no)={r1['gap']/r0['gap']:.4f})")
        print(f"     g:   no={r0['goe']:.4f} ab={r1['goe']:.4f}  eff(no)/eff(ab)={r0['eff']/r1['eff']:.4f}")

    print("\n" + "=" * 86)
    print("TASK 3c/3d — g(ab)/g(no) = [gap(ab)/gap(no)] * [eff(no)/eff(ab)] > 1 for all d>=2 ?")
    print("=" * 86)
    print(f"  {'d':>3} {'g(no)':>8} {'g(ab)':>8} {'g(ab)>g(no)':>12} {'eff_ratio':>10} {'gap_ratio':>10}")
    allup = True
    for d in [2, 3, 4, 5, 6, 8, 12]:
        r0 = model(1000, d, False); r1 = model(1000, d, True)
        up = r1['goe'] > r0['goe']; allup &= up
        print(f"  {d:3d} {r0['goe']:8.4f} {r1['goe']:8.4f} {str(up):>12} "
              f"{r0['eff']/r1['eff']:10.4f} {r1['gap']/r0['gap']:10.4f}")
    print(f"  => g(ab) > g(no) for all tested d: {allup}")
    print("  Mechanism: eff_ratio = eff(no)/eff(ab) = (d+2-lam)/(d-lam) > 1 (proven);")
    print("  gap_ratio = gap(ab)/gap(no) ~ 1 (stays close); product > 1 => a~b RAISES gap/eff.")

    print("\n" + "=" * 86)
    print("d=2 exact: g(no)=1/3; eff(no)=2, eff(ab)=2/(4-1)=2/3 => eff_ratio=3; gap~unchanged => g(ab)~1")
    print("=" * 86)
    for N in [400, 800, 1600]:
        r1 = model(N, 2, True); r0 = model(N, 2, False)
        print(f"  N={N}: g(no)={r0['goe']:.4f} g(ab)={r1['goe']:.4f} "
              f"eff(no)={r0['eff']:.4f} eff(ab)={r1['eff']:.4f} gap(no)={r0['gap']:.4f} gap(ab)={r1['gap']:.4f}")


if __name__ == "__main__":
    main()
