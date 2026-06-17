"""
Canonical Fiedler-complement block detector for the Required>0 regime.
Carriers C_p = smallest vertex set holding p% of ||f||^2; block B_p = V\\C_p; B = largest
connected component of G[B_p]. Test ratio = lam2(G[B])/lam2(G) >= 3 for some p, across the
full Required>0 corpus (deg2+dense, lollipops, and the 1949 random graphs from the block
round, regenerated with the same seed). Also degree-based detectors + block uniformity.
Run: python conjecture_B_canonical_detector.py
"""
import numpy as np
import networkx as nx


# ---------- core ----------
def analyze(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    Required = l2 * (l2 + S * S / m - fDf)
    return dict(nodes=nodes, n=n, m=m, l2=l2, f=f, d=d, Required=Required)


def lam2_sub(G, Bnodes):
    if len(Bnodes) < 2:
        return None, 0, []
    H = G.subgraph(Bnodes)
    comps = list(nx.connected_components(H))
    if not comps:
        return None, 0, []
    cc = max(comps, key=len)
    if len(cc) < 2:
        return 0.0, len(comps), list(cc)
    Hc = H.subgraph(cc)
    LH = nx.laplacian_matrix(Hc, nodelist=list(Hc.nodes())).toarray().astype(float)
    return float(np.linalg.eigvalsh(LH)[1]), len(comps), list(cc)


def canonical(G, R, ps=(0.5, 0.7, 0.8, 0.9)):
    nodes, f, n, l2 = R['nodes'], R['f'], R['n'], R['l2']
    idx = {v: i for i, v in enumerate(nodes)}
    f2 = f * f
    order = np.argsort(-f2)             # descending f^2
    cum = np.cumsum(f2[order])
    out = {}
    for p in ps:
        k = int(np.searchsorted(cum, p)) + 1
        k = min(max(k, 1), n - 1)
        Cidx = set(order[:k].tolist())
        Bnodes = [nodes[i] for i in range(n) if i not in Cidx]
        lamB, ncomp, cc = lam2_sub(G, Bnodes)
        ratio = (lamB / l2) if (lamB is not None and l2 > 1e-12) else None
        if cc:
            fb = np.array([f[idx[v]] for v in cc])
            massB = float((fb * fb).sum())
            mean = float(fb.mean()); std = float(fb.std())
            unif = std / abs(mean) if abs(mean) > 1e-15 else float('inf')
        else:
            massB = 0.0; unif = float('inf'); fb = np.array([])
        out[p] = dict(sizeB=len(cc), sizeC=k, massB=massB, lamB=lamB, ratio=ratio,
                      ncomp=ncomp, unif=unif, connected=(ncomp == 1))
    return out


def degree_detectors(G, R):
    nodes, d, l2 = R['nodes'], R['d'], R['l2']
    med = float(np.median(d))
    res = {}
    for name, Bn in (('deg>=med', [nodes[i] for i in range(R['n']) if d[i] >= med]),
                     ('deg>=l2', [nodes[i] for i in range(R['n']) if d[i] >= l2])):
        lamB, ncomp, cc = lam2_sub(G, Bn)
        res[name] = (lamB / l2) if (lamB is not None and l2 > 1e-12) else None
    return res


# ---------- builders (identical to block-principle round) ----------
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


def two_cycles(Lc, seed=0):
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


def random_corpus():
    rng = np.random.default_rng(7); gens = []
    for _ in range(900):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(20, 120))
        gens.append(deg2dense(n, float(rng.uniform(0.3, 0.8)), s))
    for _ in range(700):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(20, 120))
        gens.append(degk_block(n, float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 5)), s))
    for _ in range(500):
        gens.append(nx.lollipop_graph(int(rng.integers(6, 60)), int(rng.integers(2, 25))))
    for _ in range(500):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(8, 40))
        gens.append(pathend_dense(n, float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 12)), s))
    for _ in range(400):
        gens.append(two_cycles(int(rng.integers(5, 40))))
    return gens


# ---------- TASK 1: detailed on canonical families ----------
def task1():
    print("TASK 1: canonical detector on deg2+dense sweep and lollipops")
    print(f"{'family':14s} {'n':>4} {'lam2':>7} | " +
          " | ".join(f"p={int(100*p)}:rat/conn/unif" for p in (0.5, 0.8, 0.9)))
    fams = [("deg2dense", deg2dense(50, 0.65, 1)), ("deg2dense", deg2dense(200, 0.65, 2)),
            ("deg2dense", deg2dense(1000, 0.65, 3)), ("lollipop", nx.lollipop_graph(20, 5)),
            ("lollipop", nx.lollipop_graph(50, 10)), ("lollipop", nx.lollipop_graph(30, 20))]
    for nm, G in fams:
        R = analyze(G); c = canonical(G, R)
        cells = []
        for p in (0.5, 0.8, 0.9):
            x = c[p]; r = x['ratio'] if x['ratio'] else 0.0
            conn = 'Y' if x['connected'] else str(x['ncomp'])
            cells.append(f"{r:6.1f}/{conn}/{min(x['unif'], 9.99):.2f}")
        print(f"{nm:14s} {R['n']:4d} {R['l2']:7.3f} | " + " | ".join(cells))


# ---------- TASK 2/3/4: corpus aggregate ----------
def task234():
    print("\nBuilding Required>0 corpus (deg2+dense sweep + lollipops + 1949 random)...")
    corpus = []
    for n in (50, 100, 200, 500, 1000):
        corpus.append(deg2dense(n, 0.65, 100 + n))
    for m in (10, 20, 50):
        for L in (3, 5, 10, 20):
            corpus.append(nx.lollipop_graph(m, L))
    corpus += random_corpus()

    ps = (0.5, 0.7, 0.8, 0.9)
    rows = []  # per graph: dict
    for G in corpus:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        R = analyze(G)
        if R['Required'] <= 1e-9:
            continue
        c = canonical(G, R, ps)
        deg = degree_detectors(G, R)
        best_ratio = max([c[p]['ratio'] for p in ps if c[p]['ratio'] is not None] + [0.0])
        rows.append(dict(R=R, c=c, deg=deg, best=best_ratio))
    N = len(rows)
    print(f"Required>0 graphs in corpus: {N}\n")

    print("TASK 2: per-threshold reliability (ratio = lam2(G[B])/lam2(G))")
    print(f"{'p':>4} {'min ratio':>10} {'median':>8} {'%>=3':>7} {'%conn':>7}")
    for p in ps:
        rr = [r['c'][p]['ratio'] for r in rows if r['c'][p]['ratio'] is not None]
        cn = [r['c'][p]['connected'] for r in rows]
        print(f"{int(100*p):4d} {min(rr):10.2f} {np.median(rr):8.2f} "
              f"{100*np.mean([x>=3 for x in rr]):6.1f}% {100*np.mean(cn):6.1f}%")
    best_all = [r['best'] for r in rows]
    n_ge3 = sum(b >= 3 for b in best_all)
    print(f"\n  BEST-over-p ratio: min={min(best_all):.2f}, median={np.median(best_all):.2f}, "
          f">=3 for {n_ge3}/{N} ({100*n_ge3/N:.1f}%)")
    bad = [r for r in rows if r['best'] < 3]
    print(f"  graphs with best-over-p < 3: {len(bad)}")
    for r in bad[:6]:
        R = r['R']
        print(f"     n={R['n']} lam2={R['l2']:.4f} Req={R['Required']:.4f} best={r['best']:.2f}")

    print("\nTASK 3: degree-based detectors (largest CC ratio)")
    for name in ('deg>=med', 'deg>=l2'):
        rr = [r['deg'][name] for r in rows if r['deg'][name] is not None]
        print(f"  {name:9s}: min={min(rr):6.2f} median={np.median(rr):6.2f} "
              f">=3 for {100*np.mean([x>=3 for x in rr]):.1f}%")

    print("\nTASK 4: block uniformity std(f|_B)/|mean(f|_B)| at the best-ratio threshold")
    unifs = []
    for r in rows:
        ps_valid = [(r['c'][p]['ratio'], r['c'][p]['unif']) for p in ps
                    if r['c'][p]['ratio'] is not None]
        if not ps_valid:
            continue
        _, u = max(ps_valid, key=lambda t: t[0])
        unifs.append(u)
    unifs = np.array(unifs)
    for thr in (0.05, 0.1, 0.2, 0.5):
        print(f"  std/|mean| < {thr}: {100*np.mean(unifs<thr):5.1f}%")
    print(f"  median std/|mean| = {np.median(unifs):.3f}")
    # uniformity tightens with the gap ratio:
    bests = np.array([r['best'] for r in rows if any(r['c'][p]['ratio'] is not None for p in ps)])
    hi = bests >= 20
    print(f"  among high-gap (best ratio>=20, n={hi.sum()}): median std/|mean|="
          f"{np.median(unifs[hi]):.3f}, <0.1 for {100*np.mean(unifs[hi]<0.1):.1f}%")


if __name__ == "__main__":
    task1()
    task234()
