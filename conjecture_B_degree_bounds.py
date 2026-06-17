"""
Degree-based spectral bounds to close the block lemma lam2(G[B]) >= c*lam2(G), B=p80 block.
TRACK A: test Brouwer-Haemers / Kirkland / Lu-Man-Kahn / simple 2*delta-n+2 bounds (validity
 + ratio coverage). TRACK B: characterize the non-dense 30%. TRACK C: delta_B_internal/lam2(G).
TRACK D: bypass the gap -- bound relative non-uniformity ||f_B-mean||^2/||f_B||^2 via
 ||g||^2/(gamma-lam2)^2 (boundary forcing small).
Run: python conjecture_B_degree_bounds.py
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
        return None, C
    cc = max(comps, key=len)
    return (list(cc) if len(cc) >= 2 else None), C


def block_data(G, Bn, f, idx, l2):
    H = G.subgraph(Bn); b = len(Bn)
    LB = nx.laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
    gamma = float(np.linalg.eigvalsh(LB)[1])
    din = LB.diagonal(); eB = H.number_of_edges()
    dsort = np.sort(din); d1 = dsort[0]; d2 = dsort[1] if b >= 2 else dsort[0]
    bounds = {
        'BrouwerHaemers(d1+d2-b+2)': d1 + d2 - b + 2,
        'Kirkland(2e/(b-1)-(b-2))': 2 * eB / (b - 1) - (b - 2),
        'LuManKahn': float(np.sum(np.maximum(0, 2 * din - b + 1))) / (b - 1),
        'simple(2*delta-b+2)': 2 * d1 - b + 2,
    }
    # TRACK D: boundary forcing g
    fB = np.array([f[idx[v]] for v in Bn]); Bset = set(Bn)
    g = np.array([sum(f[idx[u]] - f[idx[v]] for u in G[v] if u not in Bset) for v in Bn])
    gnorm = float((g * g).sum()); massB = float((fB * fB).sum())
    mean = fB.mean(); dev = float(((fB - mean) ** 2).sum())
    pbound = gnorm / (gamma - l2) ** 2 if gamma > l2 else float('inf')
    return dict(b=b, gamma=gamma, ratio=gamma / l2, delta_B=float(d1),
                dens=2 * eB / (b * (b - 1)), bounds=bounds,
                dense_cond=(d1 > (b - 2) / 2), gnorm=gnorm, massB=massB,
                dev=dev, ru=dev / massB if massB > 0 else float('inf'),
                ru_bound=pbound / massB if massB > 0 and np.isfinite(pbound) else float('inf'))


# builders
def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def degk_block(n, q, k, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=min(k, n - 1), replace=False):
        G.add_edge(0, int(b))
    return G


def two_cycles(Lc):
    G = nx.cycle_graph(Lc); G2 = nx.relabel_nodes(nx.cycle_graph(Lc),
                                                  {i: i + Lc for i in range(Lc)})
    G = nx.union(G, G2); G.add_edge(0, Lc); return G


def pathend_dense(n, q, plen, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n, q, seed=int(rng.integers(0, 2**31)))
    attach = 0; nxt = n
    for _ in range(plen):
        G.add_edge(attach, nxt); attach = nxt; nxt += 1
    return G


def corpus():
    out = []
    for n in (50, 100, 200, 500, 1000):
        out.append(('deg2dense', deg2dense(n, 0.65, 100 + n)))
    for m in (10, 20, 50):
        for L in (3, 5, 10, 20):
            out.append(('lollipop', nx.lollipop_graph(m, L)))
    rng = np.random.default_rng(7)
    for _ in range(900):
        s = int(rng.integers(0, 2**31)); out.append(
            ('deg2dense', deg2dense(int(rng.integers(20, 120)), float(rng.uniform(0.3, 0.8)), s)))
    for _ in range(700):
        s = int(rng.integers(0, 2**31)); out.append(('degk', degk_block(
            int(rng.integers(20, 120)), float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 5)), s)))
    for _ in range(500):
        out.append(('lollipop', nx.lollipop_graph(int(rng.integers(6, 60)), int(rng.integers(2, 25)))))
    for _ in range(500):
        s = int(rng.integers(0, 2**31)); out.append(('pathend', pathend_dense(
            int(rng.integers(8, 40)), float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 12)), s)))
    for _ in range(400):
        out.append(('two_cycles', two_cycles(int(rng.integers(5, 40)))))
    return out


def main():
    print("Building corpus...")
    A = []
    for fam, G in corpus():
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        Req, l2, f, nodes = required_of(G)
        if Req <= 1e-9:
            continue
        idx = {v: i for i, v in enumerate(nodes)}
        Bn, C = p80_block(G, f, nodes)
        if Bn is None:
            continue
        bd = block_data(G, Bn, f, idx, l2)
        bd['fam'] = fam; bd['l2'] = l2; bd['Req'] = Req
        A.append(bd)
    N = len(A)
    print(f"N = {N}\n")

    print("TRACK A: degree-based bounds on lam2(G[B]) -- validity & ratio coverage")
    print(f"{'bound':28s} {'%valid':>7} {'%rat>=1':>8} {'%rat>=2':>8} {'medRatio':>9}")
    bnames = list(A[0]['bounds'].keys())
    for bn in bnames:
        vals = np.array([a['bounds'][bn] for a in A])
        gam = np.array([a['gamma'] for a in A]); l2a = np.array([a['l2'] for a in A])
        valid = vals <= gam + 1e-6
        br = vals / l2a
        print(f"{bn:28s} {100*np.mean(valid):6.1f}% {100*np.mean(br>=1):7.1f}% "
              f"{100*np.mean(br>=2):7.1f}% {np.median(br):9.2f}")
    # combined coverage: best valid bound gives ratio>=2?
    cov2 = np.zeros(N, bool); cov1 = np.zeros(N, bool)
    for i, a in enumerate(A):
        best = max((v for bn, v in a['bounds'].items() if v <= a['gamma'] + 1e-6), default=-1e9)
        cov2[i] = best >= 2 * a['l2']; cov1[i] = best >= a['l2']
    print(f"  COMBINED (best valid bound): ratio>=1 for {100*np.mean(cov1):.1f}%, "
          f"ratio>=2 for {100*np.mean(cov2):.1f}%")

    print("\nTRACK B: the non-dense blocks (delta_B <= (|B|-2)/2)")
    nd = [a for a in A if not a['dense_cond']]
    print(f"  count: {len(nd)}/{N} ({100*len(nd)/N:.1f}%)")
    if nd:
        from collections import Counter
        fc = Counter(a['fam'] for a in nd)
        print(f"  families: {dict(fc)}")
        rr = np.array([a['ratio'] for a in nd])
        print(f"  their actual ratio: min={rr.min():.2f} median={np.median(rr):.2f} "
              f">=2.5 for {100*np.mean(rr>=2.5):.1f}%, >=2 for {100*np.mean(rr>=2):.1f}%")
        dn = np.array([a['dens'] for a in nd]); bb = np.array([a['b'] for a in nd])
        print(f"  density median={np.median(dn):.2f}, |B| median={np.median(bb):.0f}")

    print("\nTRACK C: delta_B_internal / lam2(G)  (necessary: upper-bounds lam2(B)>=... no, "
          "delta>=lam2(B))")
    dl = np.array([a['delta_B'] / a['l2'] for a in A])
    print(f"  delta_B/lam2(G): min={dl.min():.2f} median={np.median(dl):.2f} "
          f">=2 for {100*np.mean(dl>=2):.1f}%, >=2.5 for {100*np.mean(dl>=2.5):.1f}%")

    print("\nTRACK D: bypass the gap -- relative non-uniformity of f_B")
    ru = np.array([a['ru'] for a in A])             # ||f_B-mean||^2 / ||f_B||^2 (actual)
    rub = np.array([a['ru_bound'] for a in A])      # ||g||^2/((gamma-l2)^2 ||f_B||^2) (bound)
    print(f"  ACTUAL ||f_B-mean||^2/||f_B||^2: median={np.median(ru):.3f} max={ru.max():.3f}; "
          f"<0.1 for {100*np.mean(ru<0.1):.1f}%, <0.3 for {100*np.mean(ru<0.3):.1f}%")
    fin = np.isfinite(rub)
    print(f"  BOUND ||g||^2/((gamma-l2)^2||f_B||^2): median={np.median(rub[fin]):.3f} "
          f"max={rub[fin].max():.3f}; <0.5 for {100*np.mean(rub[fin]<0.5):.1f}%, "
          f"<1 for {100*np.mean(rub[fin]<1):.1f}%")
    print(f"  bound is finite (gamma>lam2) for {100*np.mean(fin):.1f}% (=block principle ratio>1)")
    # is ||g||^2 itself bounded relative to massB? g ~ carrier values on boundary
    gn = np.array([a['gnorm'] / a['massB'] for a in A if a['massB'] > 0])
    print(f"  ||g||^2/||f_B||^2: median={np.median(gn):.2f} max={gn.max():.2f} "
          f"(boundary forcing relative to block mass)")


if __name__ == "__main__":
    main()
