"""
Test the general block principle for Required > 0: does every Required>0 graph have a
well-connected block B with lam2(G[B]) >> lam2(G)?

Key identity: lam2 = fDf - fAf (f=Fiedler), so Required = lam2(lam2+S^2/m-fDf) > 0
<=> fDf < lam2 + S^2/m <=> fAf < S^2/m. Regular graphs: S=0, fAf=d-lam2>0 => Required<0
ALWAYS. So irregularity is NECESSARY (TASK 3). We test sufficiency and the block principle
on adversarial triangle-rich / sparse families that lack an obvious dense block.
Run: python conjecture_B_block_principle.py
"""
import numpy as np
import networkx as nx


# ---------- core quantities ----------
def analyze(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f); fAf = float(f @ A @ f)
    A2 = A @ A; W = A * A2
    T = float(f @ (np.diag(W @ np.ones(n)) - W) @ f)
    RHS = l2 * (2 * fDf - l2 - S * S / m)
    Required = l2 * (l2 + S * S / m - fDf)
    Deficit = l2 * fDf - T
    return dict(n=n, m=m, l2=l2, f=f, d=d, A=A, fDf=fDf, S=S, fAf=fAf, T=T,
                RHS=RHS, Required=Required, Deficit=Deficit,
                B=bool(T <= RHS + 1e-9 * max(1.0, abs(RHS))))


def block_gap(G, Bnodes):
    Bnodes = [v for v in Bnodes]
    if len(Bnodes) < 2:
        return None, len(Bnodes)
    H = G.subgraph(Bnodes)
    comps = list(nx.connected_components(H))
    if not comps:
        return None, 0
    cc = max(comps, key=len)
    if len(cc) < 2:
        return 0.0, len(cc)
    Hc = H.subgraph(cc)
    LH = nx.laplacian_matrix(Hc, nodelist=list(Hc.nodes())).toarray().astype(float)
    return float(np.linalg.eigvalsh(LH)[1]), len(cc)


def blocks(G, R):
    f, d, n = R['f'], R['d'], R['n']
    nodes = list(G.nodes())
    med = float(np.median(d))
    hi = [nodes[i] for i in range(n) if d[i] > med]                 # (a) high-degree
    try:
        bicomp = max(nx.biconnected_components(G), key=len)         # (b) largest 2-connected
    except Exception:
        bicomp = set()
    noncar = [nodes[i] for i in range(n) if f[i] ** 2 < 1.0 / n]    # (c) non-carriers
    out = {}
    for name, Bn in (('hi-deg', hi), ('2conn', list(bicomp)), ('non-carr', noncar)):
        g, sz = block_gap(G, Bn)
        out[name] = (g, sz)
    return out


def ratios(G, R):
    bl = blocks(G, R); l2 = R['l2']
    rs = {}
    best = 0.0
    for name, (g, sz) in bl.items():
        r = (g / l2) if (g is not None and l2 > 1e-12) else None
        rs[name] = r
        if r is not None:
            best = max(best, r)
    return rs, best


# ---------- builders ----------
def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def triangle_cactus(k):  # k triangles in a chain, consecutive share one vertex
    G = nx.Graph(); prev = 0; idx = 1
    for _ in range(k):
        a, b, c = prev, idx, idx + 1
        G.add_edges_from([(a, b), (b, c), (a, c)]); prev = c; idx += 2
    return G


def rand_tree(t, rng):
    G = nx.Graph(); G.add_node(0)
    for v in range(1, t):
        G.add_edge(v, int(rng.integers(0, v)))
    return G


def triangulated_tree(t, seed):  # each tree edge -> triangle (add apex adjacent to both)
    rng = np.random.default_rng(seed); T = rand_tree(t, rng); G = nx.Graph(T); nxt = t
    for (u, v) in list(T.edges()):
        G.add_edge(u, nxt); G.add_edge(v, nxt); nxt += 1
    return G


def powerlaw_config(n, seed, gamma=2.5):
    rng = np.random.default_rng(seed)
    deg = (rng.pareto(gamma - 1, n) + 1).astype(int) + 1
    deg = np.clip(deg, 1, n - 1)
    if deg.sum() % 2: deg[0] += 1
    G = nx.configuration_model(deg, seed=int(rng.integers(0, 2**31)))
    G = nx.Graph(G); G.remove_edges_from(nx.selfloop_edges(G))
    cc = max(nx.connected_components(G), key=len)
    return nx.convert_node_labels_to_integers(G.subgraph(cc))


def expander_pendants(n, npend, seed):
    rng = np.random.default_rng(seed)
    if n % 2: n += 1  # 3-regular needs n*3 even
    G = nx.random_regular_graph(3, n, seed=int(rng.integers(0, 2**31)))
    G = nx.Graph(G); nxt = n
    for v in rng.choice(range(n), size=npend, replace=False):
        G.add_edge(int(v), nxt); nxt += 1
    return G


def book(k):  # k triangles sharing the spine edge (0,1)
    G = nx.Graph(); G.add_edge(0, 1)
    for i in range(k):
        v = 2 + i; G.add_edge(0, v); G.add_edge(1, v)
    return G


def friendship(k):  # k triangles sharing hub 0 (windmill Wd(3,k))
    G = nx.Graph()
    for i in range(k):
        a, b = 1 + 2 * i, 2 + 2 * i
        G.add_edge(0, a); G.add_edge(0, b); G.add_edge(a, b)
    return G


def windmill4(k):  # k copies of K4 sharing hub 0 (HAS dense blocks: control)
    G = nx.Graph()
    for i in range(k):
        vs = [0, 1 + 3 * i, 2 + 3 * i, 3 + 3 * i]
        for x in range(4):
            for y in range(x + 1, 4):
                G.add_edge(vs[x], vs[y])
    return G


# ---------- TASK 1: prior Required>0 families ----------
def task1():
    print("TASK 1: block ratio lam2(G[B])/lam2(G) on prior Required>0 families")
    print(f"{'family':16s} {'n':>4} {'lam2':>8} {'Req':>9} {'B':>2} {'Def/Req':>8} "
          f"{'hi-deg':>8} {'2conn':>8} {'non-carr':>9} {'BEST':>7}")
    fams = [("deg2dense100", deg2dense(100, 0.65, 300)),
            ("deg2dense200", deg2dense(200, 0.65, 500)),
            ("lollipop20_5", nx.lollipop_graph(20, 5)),
            ("lollipop50_10", nx.lollipop_graph(50, 10))]
    for nm, G in fams:
        R = analyze(G); rs, best = ratios(G, R)
        dr = R['Deficit'] / R['Required'] if abs(R['Required']) > 1e-12 else float('nan')
        def fmt(x): return f"{x:8.1f}" if x is not None else f"{'--':>8}"
        print(f"{nm:16s} {R['n']:4d} {R['l2']:8.4f} {R['Required']:9.4f} "
              f"{'Y' if R['B'] else 'N':>2} {dr:8.2f} {fmt(rs['hi-deg'])} {fmt(rs['2conn'])} "
              f"{fmt(rs['non-carr']):>9} {best:7.1f}")


# ---------- TASK 2: adversarial families ----------
def task2():
    print("\nTASK 2: adversarial triangle-rich / sparse families (no obvious dense block)")
    print(f"{'family':18s} {'n':>4} {'lam2':>8} {'fAf':>8} {'S^2/m':>7} {'Req':>9} "
          f"{'Req>0':>5} {'B':>2} {'Def/Req':>8} {'2conn':>8} {'BEST':>7}")
    fams = []
    for k in (5, 10, 20, 40): fams.append((f"tri-cactus k={k}", triangle_cactus(k)))
    for s in (1, 2, 3): fams.append((f"tri-tree t=20 s={s}", triangulated_tree(20, s)))
    for s in (1, 2, 3): fams.append((f"tri-tree t=50 s={s}", triangulated_tree(50, s)))
    for s in (1, 2): fams.append((f"powerlaw n~80 s={s}", powerlaw_config(80, s)))
    for s in (1, 2): fams.append((f"powerlaw n~150 s={s}", powerlaw_config(150, s)))
    for s in (1, 2): fams.append((f"expand+pend n=30 s={s}", expander_pendants(30, 10, s)))
    for k in (5, 15, 30): fams.append((f"book k={k}", book(k)))
    for k in (5, 15, 30): fams.append((f"friendship k={k}", friendship(k)))
    for k in (3, 8): fams.append((f"windmill4 k={k}", windmill4(k)))
    for nm, G in fams:
        R = analyze(G); rs, best = ratios(G, R)
        dr = R['Deficit'] / R['Required'] if abs(R['Required']) > 1e-12 else float('nan')
        twoc = rs['2conn']
        print(f"{nm:18s} {R['n']:4d} {R['l2']:8.4f} {R['fAf']:8.4f} {R['S']**2/R['m']:7.3f} "
              f"{R['Required']:9.4f} {'Y' if R['Required']>1e-9 else 'n':>5} "
              f"{'Y' if R['B'] else 'N':>2} {dr:8.2f} "
              f"{(f'{twoc:8.1f}' if twoc is not None else f'{chr(45)*2:>8}')} {best:7.1f}")


# --- generators that DO produce Required>0, + the telling 'two non-dense blocks' probe ---
def degk_block(n, q, k, seed):  # low-deg-k vertex attached to dense G(n-1,q)
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=min(k, n - 1), replace=False):
        G.add_edge(0, int(b))
    return G


def two_cycles(L, seed=0):  # two L-cycles joined by ONE edge: bottleneck, NON-dense blocks
    G = nx.cycle_graph(L); G2 = nx.cycle_graph(L)
    G2 = nx.relabel_nodes(G2, {i: i + L for i in range(L)})
    G = nx.union(G, G2); G.add_edge(0, L)
    return G


def pathend_dense(n, q, plen, seed):  # dense block + pendant PATH (lollipop-like, generic block)
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n, q, seed=int(rng.integers(0, 2**31)))
    attach = 0; nxt = n
    for _ in range(plen):
        G.add_edge(attach, nxt); attach = nxt; nxt += 1
    return G


def task3_4():
    print("\nTASK 3/4: search min BEST-block-ratio among Required>0 graphs")
    print("  (key id: Required>0 <=> fAf < S^2/m; regular => S=0,fAf=d-lam2>0 => Req<0)")
    rng = np.random.default_rng(7)
    found = 0; reg_viol = 0; worst = None; below3 = []
    gens = []
    for _ in range(900):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(20, 120))
        q = float(rng.uniform(0.3, 0.8)); gens.append(('deg2dense', deg2dense(n, q, s)))
    for _ in range(700):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(20, 120))
        q = float(rng.uniform(0.3, 0.8)); k = int(rng.integers(1, 5))
        gens.append(('degk', degk_block(n, q, k, s)))
    for _ in range(500):
        m = int(rng.integers(6, 60)); L = int(rng.integers(2, 25))
        gens.append(('lollipop', nx.lollipop_graph(m, L)))
    for _ in range(500):
        s = int(rng.integers(0, 2**31)); n = int(rng.integers(8, 40))
        q = float(rng.uniform(0.3, 0.8)); pl = int(rng.integers(1, 12))
        gens.append(('pathend', pathend_dense(n, q, pl, s)))
    for _ in range(400):
        gens.append(('two_cycles', two_cycles(int(rng.integers(5, 40)))))
    for nm, G in gens:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        R = analyze(G)
        degs = [G.degree(v) for v in G.nodes()]
        if max(degs) == min(degs) and R['Required'] > 1e-9:
            reg_viol += 1
        if R['Required'] <= 1e-9:
            continue
        found += 1
        rs, best = ratios(G, R)
        if worst is None or best < worst[0]:
            worst = (best, nm, R, rs)
        if best < 3.0:
            below3.append((nm, best, R['n'], R['l2'], R['Required'],
                           R['Deficit'] / R['Required'], R['B'], rs))
    print(f"  Required>0 graphs found: {found} ; regular-with-Req>0 (must be 0): {reg_viol}")
    if worst:
        b, nm, R, rs = worst
        print(f"  MIN best-block-ratio = {b:.2f}  [{nm}] n={R['n']} lam2={R['l2']:.4f} "
              f"Req={R['Required']:.4f} Def/Req={R['Deficit']/R['Required']:.2f} B={R['B']}")
        print(f"     ratios hi-deg={rs['hi-deg']}, 2conn={rs['2conn']}, "
              f"non-carr={rs['non-carr']}")
    print(f"  Required>0 graphs with BEST block ratio < 3: {len(below3)}")
    for nm, b, n, l2, req, dr, Bh, rs in below3[:8]:
        print(f"     [{nm}] n={n} best={b:.2f} lam2={l2:.4f} Req={req:.4f} "
              f"Def/Req={dr:.2f} B={Bh} 2conn={rs['2conn']} hi-deg={rs['hi-deg']}")


if __name__ == "__main__":
    task1()
    task2()
    task3_4()
