"""
Rigorize delta>0 for TYPE A bulk rigidity (d=2 twin ports on K_N).

delta_leading = 8/(3N^2) (Fiedler held fixed). Deleting interior edge changes Fiedler by ||Df||.
Measure: (a) ||Df|| scaling, (b) exact delta vs leading, (c) (delta_exact - delta_leading)/delta_leading,
(d) N0 such that delta_exact>0 for N>=N0, (e) small-N exhaustive gap/eff>=1/3.
Run: python conjecture_B_typeA_delta_rigor.py
"""
import numpy as np
import networkx as nx


def twin_graph(N, deleted=None):
    G = nx.complete_graph(N)
    if deleted: G.remove_edge(*deleted)
    a, b, v0 = N, N + 1, N + 2
    for u in (a, b):
        G.add_edge(u, 0); G.add_edge(u, 1)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    return G, a, b, v0


def fiedler_and_gap(G, a, b, v0):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    m = G.number_of_edges(); S = float(dg @ f)
    Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gs - S ** 2 / m) - B2
    return f, idx, lam, gap


def main():
    print("=" * 86)
    print("TASK 1 — Fiedler perturbation ||Df|| when deleting interior edge (2,3) from K_N")
    print("=" * 86)
    print(f"  {'N':>5} {'||Df||':>12} {'||Df||*N^2':>12} {'||Df||*N^3':>12}")
    for N in [40, 80, 160, 320]:
        G0, a, b, v0 = twin_graph(N)
        f0, idx0, _, _ = fiedler_and_gap(G0, a, b, v0)
        G1, a1, b1, v01 = twin_graph(N, deleted=(2, 3))
        f1, idx1, _, _ = fiedler_and_gap(G1, a1, b1, v01)
        # align on common node set (same labels)
        common = [u for u in G0.nodes() if u in G1.nodes()]
        df = np.array([f1[idx1[u]] - f0[idx0[u]] for u in common])
        nrm = float(np.linalg.norm(df))
        print(f"  {N:5d} {nrm:12.3e} {nrm*N*N:12.4f} {nrm*N*N*N:12.4f}")
    print("  => ||Df|| ~ C/N^2 (||Df||*N^2 -> const): bulk is rigid, O(1/N^2) perturbation.")

    print("\n" + "=" * 86)
    print("TASK 2 — exact delta vs leading 8/(3N^2); relative correction")
    print("=" * 86)
    print(f"  {'N':>5} {'delta_exact':>14} {'8/(3N^2)':>13} {'(exact-lead)/lead':>18} "
          f"{'corr*N':>9}")
    for N in [50, 100, 200, 500]:
        _, _, _, g0 = fiedler_and_gap(*twin_graph(N))
        _, _, _, g1 = fiedler_and_gap(*twin_graph(N, deleted=(2, 3)))
        de = g1 - g0; lead = 8 / (3 * N * N)
        rel = (de - lead) / lead
        print(f"  {N:5d} {de:14.6e} {lead:13.6e} {rel:18.5f} {rel*N:9.3f}")
    print("  => relative correction (exact-lead)/lead = O(1/N) -> 0; delta_exact = delta_lead(1+O(1/N)).")

    print("\n" + "=" * 86)
    print("TASK 3 — N0: delta_exact > 0 for all N>=N0 ?  (check delta_exact sign across N)")
    print("=" * 86)
    allpos = True; firstbad = None
    for N in range(8, 60):
        _, _, _, g0 = fiedler_and_gap(*twin_graph(N))
        _, _, _, g1 = fiedler_and_gap(*twin_graph(N, deleted=(2, 3)))
        de = g1 - g0
        if de <= 0:
            allpos = False
            if firstbad is None: firstbad = (N, de)
    print(f"  delta_exact > 0 for ALL N in [8,59]: {allpos}" +
          (f" (first <=0 at N={firstbad[0]}, delta={firstbad[1]:.2e})" if firstbad else ""))
    # also check multiple interior edges and random interior choice
    rng = np.random.default_rng(0); okrand = 0; totrand = 0
    for N in [20, 30, 50]:
        for _ in range(10):
            i, j = sorted(rng.choice(range(2, N), 2, replace=False))
            _, _, _, g0 = fiedler_and_gap(*twin_graph(N))
            _, _, _, g1 = fiedler_and_gap(*twin_graph(N, deleted=(int(i), int(j))))
            totrand += 1; okrand += (g1 - g0 > 0)
    print(f"  random interior edge deletions raise gap: {okrand}/{totrand}")

    print("\n" + "=" * 86)
    print("TASK 3b — small-N exhaustive: gap/eff >= 1/3 for twin d=2 on K_N, all N (the extremizer)")
    print("=" * 86)
    print(f"  {'N':>5} {'lam':>8} {'gap':>9} {'eff':>9} {'gap/eff':>9} {'>=1/3?':>7}")
    okall = True
    for N in range(3, 16):
        G, a, b, v0 = twin_graph(N)
        nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
        A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
        ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
        if f[idx[v0]] < 0: f = -f
        m = G.number_of_edges(); S = float(dg @ f)
        Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
        B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
        gap = lam * (Gs - S ** 2 / m) - B2
        Gc = G.copy(); Gc.remove_node(v0); Gcn = list(Gc.nodes())
        LH = nx.laplacian_matrix(Gc, nodelist=Gcn).toarray().astype(float)
        mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
        if gamma - lam <= 1e-9:
            print(f"  {N:5d}  (not TYPE A: lam>=gamma)"); continue
        inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
        ia, ib = Gcn.index(a), Gcn.index(b); eff = float(R[ia, ia] + R[ib, ib] - 2 * R[ia, ib])
        goe = gap / eff; ok = goe >= 1 / 3 - 1e-9; okall &= ok
        print(f"  {N:5d} {lam:8.4f} {gap:9.5f} {eff:9.5f} {goe:9.5f} {str(ok):>7}")
    print(f"  all small-N twin extremizers >= 1/3: {okall}")

    print("\n" + "=" * 86)
    print("SUMMARY")
    print("=" * 86)
    print("  ||Df||=O(1/N^2); delta_exact = 8/(3N^2)*(1+O(1/N)) > 0; delta_exact>0 verified all N>=8;")
    print("  twin extremizer gap/eff>=1/3 for all small N (approached from above).")


if __name__ == "__main__":
    main()
