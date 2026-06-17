"""
Test the raw edge-expansion lemma phi_raw(B) >= c*lam2(G) for the carrier-complement block.
phi_raw(B) = min_{S subset B, |S|<=|B|/2} |bnd_B(S)|/|S| (NP-hard; exact for |B|<=15 by bitmask).
Rigorous lower bound (Mohar): phi_raw(B) >= lam2(G[B])/2. Heuristic upper bound: Fiedler sweep
on B + singletons. Goal: confirm/refute phi_raw(B) >= c*lam2(G), universal c>0; measure c.
Run: python conjecture_B_edge_expansion.py
"""
import numpy as np
import networkx as nx


def required_of(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    return l2 * (l2 + S * S / m - fDf), l2, f, nodes


def p80_block(G, f, nodes, p=0.8):
    order = np.argsort(-(f * f)); cum = np.cumsum((f * f)[order])
    k = min(max(int(np.searchsorted(cum, p)) + 1, 1), len(nodes) - 1)
    C = set(nodes[order[i]] for i in range(k))
    H = G.subgraph([v for v in nodes if v not in C])
    comps = list(nx.connected_components(H))
    if not comps:
        return None
    cc = max(comps, key=len)
    return list(cc) if len(cc) >= 2 else None


def phi_exact(H, Bn):
    b = len(Bn); idx = {v: i for i, v in enumerate(Bn)}
    adj = [0] * b
    for a, c in H.edges():
        adj[idx[a]] |= (1 << idx[c]); adj[idx[c]] |= (1 << idx[a])
    half = b // 2; best = float('inf')
    for s in range(1, 1 << b):
        sz = bin(s).count('1')
        if sz > half:
            continue
        bnd = 0; ss = s
        while ss:
            v = (ss & -ss).bit_length() - 1; ss &= ss - 1
            bnd += bin(adj[v] & ~s).count('1')
        r = bnd / sz
        if r < best:
            best = r
    return best


def phi_heuristic_ub(H, Bn):
    # Fiedler sweep prefixes + singletons -> upper bound on phi_raw
    b = len(Bn); idx = {v: i for i, v in enumerate(Bn)}
    LB = nx.laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
    deg = LB.diagonal()
    fB = np.linalg.eigh(LB)[1][:, 1]
    order = np.argsort(fB)
    inS = [False] * b; bnd = 0; best = float(deg.min())  # singleton min
    half = b // 2
    for k in range(b - 1):
        v = order[k]; inS[v] = True
        for u in H[Bn[v]]:
            j = idx[u]
            bnd += -1 if inS[j] else 1
        sz = k + 1
        if sz <= half:
            best = min(best, bnd / sz)
    return best


def main():
    print("Building corpus (deg2+dense, lollipops, 1949 random)...")
    rng = np.random.default_rng(7)

    def deg2dense(n, q, seed):
        r = np.random.default_rng(seed)
        G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
        G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
        for bb in r.choice(range(1, n), size=2, replace=False):
            G.add_edge(0, int(bb))
        return G

    def degk(n, q, k, seed):
        r = np.random.default_rng(seed)
        G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
        G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
        for bb in r.choice(range(1, n), size=min(k, n - 1), replace=False):
            G.add_edge(0, int(bb))
        return G

    def two_cycles(Lc):
        G = nx.cycle_graph(Lc); G2 = nx.relabel_nodes(nx.cycle_graph(Lc),
                                                      {i: i + Lc for i in range(Lc)})
        G = nx.union(G, G2); G.add_edge(0, Lc); return G

    def pathend(n, q, pl, seed):
        r = np.random.default_rng(seed)
        G = nx.gnp_random_graph(n, q, seed=int(r.integers(0, 2**31)))
        at = 0; nx2 = n
        for _ in range(pl):
            G.add_edge(at, nx2); at = nx2; nx2 += 1
        return G

    corp = []
    for n in (50, 100, 200, 500):
        corp.append(deg2dense(n, 0.65, 100 + n))
    for m in (10, 20, 50):
        for L in (3, 5, 10, 20):
            corp.append(nx.lollipop_graph(m, L))
    for _ in range(900):
        corp.append(deg2dense(int(rng.integers(20, 120)), float(rng.uniform(0.3, 0.8)),
                              int(rng.integers(0, 2**31))))
    for _ in range(700):
        corp.append(degk(int(rng.integers(20, 120)), float(rng.uniform(0.3, 0.8)),
                         int(rng.integers(1, 5)), int(rng.integers(0, 2**31))))
    for _ in range(500):
        corp.append(nx.lollipop_graph(int(rng.integers(6, 60)), int(rng.integers(2, 25))))
    for _ in range(500):
        corp.append(pathend(int(rng.integers(8, 40)), float(rng.uniform(0.3, 0.8)),
                            int(rng.integers(1, 12)), int(rng.integers(0, 2**31))))
    for _ in range(400):
        corp.append(two_cycles(int(rng.integers(5, 40))))

    rows = []
    for G in corp:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        Req, l2, f, nodes = required_of(G)
        if Req <= 1e-9:
            continue
        Bn = p80_block(G, f, nodes)
        if Bn is None:
            continue
        H = G.subgraph(Bn); b = len(Bn)
        LB = nx.laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
        l2B = float(np.linalg.eigvalsh(LB)[1]); delta = float(LB.diagonal().min())
        ub = phi_heuristic_ub(H, Bn)
        lb = l2B / 2.0                          # Mohar: phi_raw >= lam2(B)/2
        exact = phi_exact(H, Bn) if b <= 15 else None
        rows.append(dict(b=b, l2=l2, l2B=l2B, delta=delta, ub=ub, lb=lb, exact=exact))
    N = len(rows)
    print(f"Required>0 graphs: {N}\n")

    l2 = np.array([r['l2'] for r in rows]); l2B = np.array([r['l2B'] for r in rows])
    ub = np.array([r['ub'] for r in rows]); lb = np.array([r['lb'] for r in rows])
    ratio = l2B / l2

    print("TASK 3+1: phi_raw(B)/lam2(G) -- rigorous lower bound (Mohar lam2_B/2) and heuristic UB")
    print(f"  rigorous LB phi_raw/lam2_G = (lam2_B/2)/lam2_G: "
          f"min={(lb/l2).min():.3f} median={np.median(lb/l2):.2f} (>=1 for "
          f"{100*np.mean(lb/l2>=1):.1f}%)")
    print(f"  heuristic UB phi_raw/lam2_G: min={(ub/l2).min():.3f} median={np.median(ub/l2):.2f}")
    print(f"  => phi_raw/lam2_G is in [LB, UB]; rigorous floor c = min(lb/l2) = {(lb/l2).min():.3f}")

    ex = [r for r in rows if r['exact'] is not None]
    if ex:
        exr = np.array([r['exact'] / r['l2'] for r in ex])
        exv = np.array([r['exact'] for r in ex]); exlb = np.array([r['lb'] for r in ex])
        print(f"\nTASK 5: EXACT phi_raw on |B|<=15 (n={len(ex)}):")
        print(f"  exact phi_raw/lam2_G: min={exr.min():.3f} median={np.median(exr):.2f} "
              f"max={exr.max():.2f}; >=1 for {100*np.mean(exr>=1):.1f}%")
        print(f"  Mohar check phi_raw >= lam2_B/2: {100*np.mean(exv>=exlb-1e-9):.1f}%; "
              f"tightness median phi_raw/(lam2_B/2) = {np.median(exv/np.maximum(exlb,1e-9)):.2f}")

    print("\nTASK 3: phi_raw(B) >= lam2(G)?  (using rigorous LB lam2_B/2 >= lam2_G <=> ratio>=2)")
    print(f"  rigorous LB certifies phi_raw>=lam2_G on {100*np.mean(lb>=l2):.1f}% (ratio>=2)")
    print(f"  heuristic UB >= lam2_G on {100*np.mean(ub>=l2):.1f}% (UB still above lam2_G)")
    if ex:
        exv = np.array([r['exact'] for r in ex]); exl2 = np.array([r['l2'] for r in ex])
        print(f"  EXACT phi_raw >= lam2_G on {100*np.mean(exv>=exl2):.1f}% of |B|<=15")

    print("\nTASK 4: compare phi_raw (UB) with other quantities (Pearson corr, ratios)")
    delta = np.array([r['delta'] for r in rows])
    print(f"  corr(phi_raw_ub, lam2_B) = {np.corrcoef(ub, l2B)[0,1]:.3f}")
    print(f"  corr(phi_raw_ub, delta_B) = {np.corrcoef(ub, delta)[0,1]:.3f}")
    print(f"  median phi_raw_ub/lam2_B = {np.median(ub/l2B):.2f} "
          f"(Cheeger: phi_raw in [lam2_B/2, ...])")
    print(f"  median phi_raw_ub/delta_B = {np.median(ub/delta):.3f}")

    print("\nWORST cases by heuristic UB/lam2_G:")
    order = np.argsort(ub / l2)
    print(f"  {'b':>4} {'lam2_G':>9} {'lam2_B':>8} {'ratio':>7} {'LB/l2':>7} {'UB/l2':>7} "
          f"{'exact/l2':>9}")
    for i in order[:8]:
        r = rows[i]
        exs = f"{r['exact']/r['l2']:.2f}" if r['exact'] is not None else "--"
        print(f"  {r['b']:4d} {r['l2']:9.4f} {r['l2B']:8.3f} {r['l2B']/r['l2']:7.2f} "
              f"{r['lb']/r['l2']:7.2f} {r['ub']/r['l2']:7.2f} {exs:>9}")


if __name__ == "__main__":
    main()
