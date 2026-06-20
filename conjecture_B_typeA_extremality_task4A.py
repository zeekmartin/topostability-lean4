"""
TASK 4A: bulk-rigidity SCAN. Test whether gap/eff >= 1/3 over general (non-complete) bulks H,
with degree-2 ports a,b (twins or disjoint), v0~{a,b}. SEARCH FOR COUNTEREXAMPLES below 1/3.

We attach two degree-2 ports a,b into a bulk H (N vertices), v0~{a,b}, and compute gap/eff.
Bulk families: K_N minus random edges; quasi-complete regular; dense ER; adversarial removals
near the port neighborhoods; low-conductance dense cores (two dense blobs).
Run: python conjecture_B_typeA_extremality_task4A.py
"""
import numpy as np
import networkx as nx


def attach_ports(H, p1, p2, q1, q2, ab=False):
    """H bulk; port a~{p1,p2}, b~{q1,q2}; v0~{a,b}. Returns G,a,b,v0 or None."""
    H = nx.convert_node_labels_to_integers(H); N = H.number_of_nodes()
    G = nx.Graph(H); a, b, v0 = N, N + 1, N + 2
    G.add_node(a); G.add_node(b)
    for u in (p1, p2): G.add_edge(a, u)
    for u in (q1, q2): G.add_edge(b, u)
    if ab: G.add_edge(a, b)
    G.add_node(v0); G.add_edge(v0, a); G.add_edge(v0, b)
    return G, a, b, v0


def goe(G, a, b, v0):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); dg = A.sum(1); L = np.diag(dg) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    if f[idx[v0]] < 0: f = -f
    m = G.number_of_edges(); S = float(dg @ f)
    Gs = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(dg[idx[u]], dg[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gs - S ** 2 / m) - B2
    H = G.copy(); H.remove_node(v0); Hn = list(H.nodes())
    if not nx.is_connected(H): return None
    LH = nx.laplacian_matrix(H, nodelist=Hn).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
    if gamma - lam <= 1e-9: return None             # not TYPE A (v0 not the bottleneck)
    inv = 1.0 / (mu[1:] - lam); R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    ia, ib = Hn.index(a), Hn.index(b)
    eff = float(R[ia, ia] + R[ib, ib] - 2 * R[ia, ib])
    fv0 = float(f[idx[v0]])
    return dict(lam=lam, gamma=gamma, gap=gap, eff=eff, goe=gap / eff, fv0sq=fv0 ** 2)


def main():
    rng = np.random.default_rng(0)
    results = []   # (family, goe, lam, gamma, fv0sq)

    def add(fam, G, a, b, v0):
        r = goe(G, a, b, v0)
        if r and r['fv0sq'] > 0.3:
            results.append((fam, r['goe'], r['lam'], r['gamma'], r['fv0sq']))
        return r

    print("=" * 92)
    print("SCAN — attach degree-2 twin ports (a,b ~ {0,1}) into various dense bulks; find min gap/eff")
    print("=" * 92)

    # 1. K_N minus k random edges (twins on {0,1}, keep 0-1 intact-ish)
    for N in [30, 50, 80]:
        for kf in [0.0, 0.05, 0.1, 0.2, 0.35]:
            for s in range(3):
                H = nx.complete_graph(N); E = list(H.edges())
                k = int(kf * len(E)); drop = rng.choice(len(E), size=k, replace=False)
                for di in drop:
                    e = E[di]
                    if set(e) & {0, 1} and len(set(e) & {0, 1}) == 1: continue  # keep port nbhd-ish
                    H.remove_edge(*e)
                if not nx.is_connected(H): continue
                G, a, b, v0 = attach_ports(H, 0, 1, 0, 1)
                add(f"K{N}-{int(kf*100)}%", G, a, b, v0)

    # 2. quasi-complete regular (high degree)
    for N in [40, 60]:
        for r in [N - 5, N - 10, int(0.7 * N)]:
            if (r * N) % 2: r += 1
            if 3 <= r <= N - 1:
                H = nx.random_regular_graph(r, N, seed=int(rng.integers(1e9)))
                G, a, b, v0 = attach_ports(H, 0, 1, 0, 1)
                add(f"rr{N}_{r}", G, a, b, v0)

    # 3. dense ER
    for N in [40, 70]:
        for q in [0.5, 0.7, 0.85]:
            H = nx.gnp_random_graph(N, q, seed=int(rng.integers(1e9)))
            if nx.is_connected(H):
                G, a, b, v0 = attach_ports(H, 0, 1, 0, 1)
                add(f"ER{N}_{q}", G, a, b, v0)

    # 4. ADVERSARIAL: isolate the port neighborhood {0,1} from the rest (low local conductance)
    for N in [40, 60]:
        for keep in [2, 4, 8]:    # ports' neighbors 0,1 connect to only `keep` bulk vertices
            H = nx.complete_graph(N)
            for u in (0, 1):
                nb = [w for w in range(2, N)]
                rng.shuffle(nb)
                for w in nb[keep:]:
                    if H.has_edge(u, w): H.remove_edge(u, w)
            if not nx.is_connected(H): continue
            G, a, b, v0 = attach_ports(H, 0, 1, 0, 1)
            add(f"adv{N}_iso{keep}", G, a, b, v0)

    # 5. low-conductance: two dense blobs, ports both in one blob (or split)
    for m in [15, 25]:
        for br in [2, 4, 8]:
            B1 = nx.complete_graph(m); B2 = nx.complete_graph(m)
            H = nx.disjoint_union(B1, B2)
            for _ in range(br):
                H.add_edge(int(rng.integers(0, m)), int(m + rng.integers(0, m)))
            if not nx.is_connected(H): continue
            G, a, b, v0 = attach_ports(H, 0, 1, 0, 1)            # both ports in blob1
            add(f"2blob{m}_br{br}_same", G, a, b, v0)
            G, a, b, v0 = attach_ports(H, 0, 1, m, m + 1)        # ports split across blobs
            add(f"2blob{m}_br{br}_split", G, a, b, v0)

    # 6. disjoint ports (a~{0,1}, b~{2,3}) on dense bulks (TASK: twins are min, disjoint should be >=)
    for N in [40, 70]:
        H = nx.complete_graph(N)
        G, a, b, v0 = attach_ports(H, 0, 1, 2, 3)
        add(f"K{N}_disjoint", G, a, b, v0)
        H = nx.gnp_random_graph(N, 0.6, seed=1)
        if nx.is_connected(H):
            G, a, b, v0 = attach_ports(H, 0, 1, 2, 3)
            add(f"ER{N}.6_disjoint", G, a, b, v0)

    results.sort(key=lambda t: t[1])
    print(f"  total TYPE A samples: {len(results)}; min gap/eff = {results[0][1]:.5f} ({results[0][0]})")
    print(f"\n  LOWEST 18:")
    print(f"  {'family':22s} {'gap/eff':>9} {'lam':>7} {'gamma':>8} {'fv0^2':>7}")
    for fam, g, lam, gam, fv0 in results[:18]:
        flag = "  *** < 1/3' " if g < 1 / 3 - 1e-6 else ""
        print(f"  {fam:22s} {g:9.5f} {lam:7.4f} {gam:8.3f} {fv0:7.3f}{flag}")

    below = [t for t in results if t[1] < 1 / 3 - 1e-6]
    print(f"\n  COUNTEREXAMPLES (gap/eff < 1/3): {len(below)}")
    for t in below[:10]:
        print(f"    {t[0]}: gap/eff={t[1]:.5f} lam={t[2]:.4f} gamma={t[3]:.3f} fv0^2={t[4]:.3f}")

    print("\n" + "=" * 92)
    print("AGGREGATE PATTERN")
    print("=" * 92)
    gv = np.array([t[1] for t in results])
    print(f"  gap/eff: min={gv.min():.4f} 1%={np.percentile(gv,1):.4f} median={np.median(gv):.4f} "
          f"max={gv.max():.4f}")
    print(f"  fraction >= 1/3: {np.mean(gv >= 1/3-1e-9):.3f}")
    print(f"  twin-port complete-bulk reference: g=1/3 (extremizer). Min over scan vs 1/3:")
    print(f"    {'<1/3' if gv.min()<1/3-1e-6 else '>=1/3 (no counterexample found)'}")


if __name__ == "__main__":
    main()
