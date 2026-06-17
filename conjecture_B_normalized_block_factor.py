"""
Test the normalized factorization lam2(G[B]) ~ delta_B * lam2_norm(G[B]) for the p80 block.
For each Required>0 graph: degree_scale = delta_B/lam2(G), norm_gap = lam2_norm(G[B]),
product = degree_scale*norm_gap, actual_ratio = lam2(G[B])/lam2(G). Check product>1 and
norm_gap>=0.38 universally, validity lam2_B >= delta_B*lam2_norm_B, and what predicts norm_gap.
Run: python conjecture_B_normalized_block_factor.py
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


def sweep_cond(H, fB, Bn):
    n = len(Bn); idx = {v: i for i, v in enumerate(Bn)}
    deg = {v: H.degree(v) for v in Bn}; totvol = 2 * H.number_of_edges()
    order = np.argsort(fB); inS = [False] * n; volS = 0; cut = 0; best = float('inf')
    for k in range(n - 1):
        i = order[k]; v = Bn[i]; inS[i] = True; volS += deg[v]
        for u in H[v]:
            cut += -1 if inS[idx[u]] else 1
        den = min(volS, totvol - volS)
        if den > 0:
            best = min(best, cut / den)
    return best


def block_metrics(G, Bn, l2G):
    H = G.subgraph(Bn); b = len(Bn)
    LB = nx.laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
    ebv, eV = np.linalg.eigh(LB)            # one decomposition: l2B and fB
    l2B = float(ebv[1]); fB = eV[:, 1] / np.linalg.norm(eV[:, 1])
    NB = nx.normalized_laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
    l2n = float(np.linalg.eigvalsh(NB)[1])
    din = LB.diagonal(); delta = float(din.min()); Delta = float(din.max())
    eB = H.number_of_edges(); dens = 2 * eB / (b * (b - 1))
    cond = sweep_cond(H, fB, Bn)
    reg = delta / Delta if Delta > 0 else 0.0
    if b <= 80:                              # clustering/transitivity expensive -> gate
        cls = nx.average_clustering(H); trans = nx.transitivity(H)
    else:
        cls = trans = float('nan')
    return dict(b=b, l2B=l2B, l2n=l2n, delta=delta, dens=dens, cond=cond,
                clustering=cls, transitivity=trans, reg=reg,
                degree_scale=delta / l2G, norm_gap=l2n, product=(delta / l2G) * l2n,
                actual_ratio=l2B / l2G, valid_lb=(delta * l2n <= l2B + 1e-9))


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


def stat(name, arr):
    a = np.array(arr)
    print(f"  {name:14s}: min={a.min():7.3f} median={np.median(a):7.3f} max={a.max():9.2f}")


def main():
    print("Building corpus + normalized factorization...")
    A = []
    for fam, G in corpus():
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        Req, l2, f, nodes = required_of(G)
        if Req <= 1e-9:
            continue
        Bn = p80_block(G, f, nodes)
        if Bn is None:
            continue
        m = block_metrics(G, Bn, l2)
        m['fam'] = fam
        A.append(m)
    N = len(A)
    print(f"N = {N}\n")

    print("FACTORIZATION quantities:")
    stat('degree_scale', [a['degree_scale'] for a in A])
    stat('norm_gap', [a['norm_gap'] for a in A])
    stat('product', [a['product'] for a in A])
    stat('actual_ratio', [a['actual_ratio'] for a in A])

    prod = np.array([a['product'] for a in A]); ng = np.array([a['norm_gap'] for a in A])
    ar = np.array([a['actual_ratio'] for a in A])
    valid = np.array([a['valid_lb'] for a in A])
    print(f"\n  product > 1 for {100*np.mean(prod > 1):.1f}% (min product = {prod.min():.3f})")
    print(f"  norm_gap >= 0.38 for {100*np.mean(ng >= 0.38):.1f}% (min norm_gap = {ng.min():.3f})")
    print(f"  validity lam2_B >= delta_B*lam2_norm_B: {100*np.mean(valid):.1f}% "
          f"(=> product <= actual_ratio when valid)")
    print(f"  product <= actual_ratio: {100*np.mean(prod <= ar + 1e-9):.1f}%")
    print(f"  product certifies ratio>=1: {100*np.mean(prod >= 1):.1f}%, "
          f">=2: {100*np.mean(prod >= 2):.1f}%")

    print("\nWORST cases (smallest product):")
    order = np.argsort(prod)
    print(f"  {'fam':12s} {'b':>4} {'deg_sc':>7} {'norm_gap':>8} {'product':>7} "
          f"{'actual':>7} {'dens':>5} {'cond':>5}")
    for i in order[:8]:
        a = A[i]
        print(f"  {a['fam']:12s} {a['b']:4d} {a['degree_scale']:7.2f} {a['norm_gap']:8.3f} "
              f"{a['product']:7.3f} {a['actual_ratio']:7.2f} {a['dens']:5.2f} {a['cond']:5.2f}")
    from collections import Counter
    lowprod = [A[i]['fam'] for i in order[:int(0.05*N)]]
    print(f"  families in lowest-5% product: {dict(Counter(lowprod))}")

    print("\nWhat predicts norm_gap? (Pearson corr with lam2_norm_B)")
    for key in ('cond', 'clustering', 'transitivity', 'dens', 'reg'):
        v = np.array([a[key] for a in A]); msk = np.isfinite(v) & np.isfinite(ng)
        print(f"  corr(norm_gap, {key:12s}) = {np.corrcoef(ng[msk], v[msk])[0,1]:+.3f} "
              f"(n={msk.sum()})")
    # Cheeger sanity: norm_gap in [cond^2/2, 2*cond]
    cond = np.array([a['cond'] for a in A])
    print(f"  Cheeger check: norm_gap >= cond^2/2 for {100*np.mean(ng >= cond**2/2 - 1e-9):.1f}%, "
          f"norm_gap <= 2*cond for {100*np.mean(ng <= 2*cond + 1e-9):.1f}%")
    print(f"  norm_gap vs conductance: median norm_gap/cond = "
          f"{np.median(ng/np.maximum(cond,1e-9)):.2f}")


if __name__ == "__main__":
    main()
