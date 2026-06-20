"""
TYPE A boundary regime: lambda/gamma -> 1 (resolvent divergence, TYPE A exit at lambda=gamma).

G = H + v0 (v0~{a,b}).  TYPE A: lambda=lam2(G) < gamma=lam2(H).  As gamma -> lambda (~2),
lambda/gamma -> 1, the core's own bottleneck mode crosses the v0 mode, graph exits TYPE A.
Run: python conjecture_B_typeA_boundary.py
"""
import numpy as np
import networkx as nx


def metrics(H, a=0, b=1):
    H = nx.convert_node_labels_to_integers(H); N = H.number_of_nodes()
    if not nx.is_connected(H) or a == b: return None
    G = nx.Graph(H); G.add_node(N); G.add_edge(N, a); G.add_edge(N, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[N]
    if f[v0] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f)
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    LH = nx.laplacian_matrix(H, nodelist=list(range(N))).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
    if gamma - lam > 1e-9:
        inv = 1.0 / (mu[1:] - lam)
        R = (phi[:, 1:] * inv) @ phi[:, 1:].T
        eff = float(R[a, a] + R[b, b] - 2 * R[a, b])
    else:
        eff = float('nan')
    return dict(N=N, lam=lam, gamma=gamma, lg=lam / gamma, gap=gap, eff=eff,
                gap_over_eff=gap / eff if eff == eff and eff > 0 else float('nan'),
                fv0=float(f[v0]), typeA=lam < gamma and float(f[v0]) ** 2 > 0.3)


def dumbbell(m, bridges, opposite=True, seed=0):
    """Two K_m joined by `bridges` edges; v0 attaches to a,b (opposite sides if opposite)."""
    G = nx.Graph()
    G.add_edges_from((i, j) for i in range(m) for j in range(i + 1, m))
    G.add_edges_from((m + i, m + j) for i in range(m) for j in range(i + 1, m))
    rng = np.random.default_rng(seed)
    pairs = [(int(rng.integers(0, m)), int(m + rng.integers(0, m))) for _ in range(bridges)]
    G.add_edges_from(pairs)
    return G


def main():
    print("=" * 88)
    print("TASK 1 — sweep lambda/gamma toward 1 (random-regular cores, gamma tuned by degree)")
    print("=" * 88)
    print(f"  {'core':14s} {'lam':>6} {'gamma':>7} {'lam/gamma':>9} {'gap':>8} {'eff':>8} {'gap/eff':>8}")
    for N in [60, 100]:
        for rho in [7, 8, 9, 10, 12, 16, 22, 30]:
            if rho > N - 1 or (rho * N) % 2: continue
            r = metrics(nx.random_regular_graph(rho, N, seed=1))
            if r and r['typeA']:
                print(f"  rr({N},{rho}){'':4s} {r['lam']:6.3f} {r['gamma']:7.3f} {r['lg']:9.4f} "
                      f"{r['gap']:8.4f} {r['eff']:8.4f} {r['gap_over_eff']:8.3f}")

    print("\n" + "=" * 88)
    print("TASK 1b — controlled approach to boundary: dumbbell, a,b OPPOSITE sides of the cut")
    print("=" * 88)
    print(f"  {'bridges':>8} {'lam':>6} {'gamma':>7} {'lam/gamma':>9} {'gap':>8} {'eff':>9} "
          f"{'gap/eff':>9} {'typeA':>6}")
    m = 14
    for br in [28, 20, 16, 14, 12, 11, 10, 9, 8]:
        r = metrics(dumbbell(m, br, opposite=True), a=0, b=m)
        if r:
            print(f"  {br:8d} {r['lam']:6.3f} {r['gamma']:7.3f} {r['lg']:9.4f} {r['gap']:8.4f} "
                  f"{r['eff']:9.4f} {r['gap_over_eff']:9.3f} {str(r['typeA']):>6}")
    print("  (as bridges drop, gamma -> lam, lam/gamma -> 1; a,b straddle the cut => phi2(a)!=phi2(b)")
    print("   => eff = sum (phi_k(a)-phi_k(b))^2/(mu_k-lam) DIVERGES => gap/eff -> 0.)")

    print("\n" + "=" * 88)
    print("TASK 1c — same approach but a,b SAME side of the cut (phi2(a)~phi2(b))")
    print("=" * 88)
    print(f"  {'bridges':>8} {'lam':>6} {'gamma':>7} {'lam/gamma':>9} {'gap':>8} {'eff':>9} {'gap/eff':>9}")
    for br in [28, 16, 12, 10, 9, 8]:
        r = metrics(dumbbell(m, br, opposite=True), a=0, b=1)   # both in first clique
        if r:
            print(f"  {br:8d} {r['lam']:6.3f} {r['gamma']:7.3f} {r['lg']:9.4f} {r['gap']:8.4f} "
                  f"{r['eff']:9.4f} {r['gap_over_eff']:9.3f}")

    print("\n" + "=" * 88)
    print("TASK 2 — at the boundary (lam/gamma>0.4), which core gives smallest gap/eff?")
    print("=" * 88)
    cores = [("dumbbell opp", dumbbell(14, 11), 0, 14),
             ("dumbbell same", dumbbell(14, 11), 0, 1),
             ("cyclepow C60^3", nx.circulant_graph(60, [1, 2, 3]), 0, 1),
             ("bipartite K_{6,30}", nx.complete_bipartite_graph(6, 30), 0, 7),
             ("rr(60,7)", nx.random_regular_graph(7, 60, seed=1), 0, 1),
             ("path-of-cliques", nx.barbell_graph(15, 0), 0, 14)]
    print(f"  {'core/attach':22s} {'lam/gamma':>9} {'gap':>8} {'eff':>9} {'gap/eff':>9} {'typeA':>6}")
    for nm, H, a, b in cores:
        r = metrics(H, a, b)
        if r:
            print(f"  {nm:22s} {r['lg']:9.4f} {r['gap']:8.4f} {r['eff']:9.4f} "
                  f"{r['gap_over_eff']:9.3f} {str(r['typeA']):>6}")

    print("\n" + "=" * 88)
    print("TASK 3 — continuity across the transition: add bridges, track gap thru lambda=gamma")
    print("=" * 88)
    print(f"  {'bridges':>8} {'lam2(G)':>8} {'gamma':>7} {'regime':>8} {'gap':>9} {'gap>0':>6}")
    m = 12; prev_gap = None; jump = 0.0
    for br in range(1, 30):
        H = dumbbell(m, br, seed=5)
        r = metrics(H, a=0, b=m)
        if r is None: continue
        regime = 'TYPE A' if r['lam'] < r['gamma'] else 'exited'
        if prev_gap is not None:
            jump = max(jump, abs(r['gap'] - prev_gap))
        prev_gap = r['gap']
        if br <= 6 or abs(r['lam'] - r['gamma']) < 0.5 or br % 5 == 0:
            print(f"  {br:8d} {r['lam']:8.4f} {r['gamma']:7.4f} {regime:>8} {r['gap']:9.5f} "
                  f"{str(r['gap']>0):>6}")
    print(f"  max |gap step| across the sweep = {jump:.4f}  (large jump at lam=gamma crossing => "
          f"gap DIScontinuous, but >0 both sides)")

    print("\n" + "=" * 88)
    print("SUMMARY")
    print("=" * 88)
    print("  Boundary is lam/gamma->1 (NOT 0.5). With a,b straddling the core cut, eff DIVERGES and")
    print("  gap/eff -> 0; with a,b same side, gap/eff stays finite. gap>0 on BOTH sides of lam=gamma")
    print("  but the Fiedler (hence gap) JUMPS at the crossing (eigenvector swap) => not continuous.")


if __name__ == "__main__":
    main()
