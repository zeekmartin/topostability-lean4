"""
Final lemma: removing the p=80% Fiedler carriers C restores a large spectral gap,
lam2(G[B]) >= c*lam2(G), B = largest CC of G\\C.
TASK1 Cheeger: sweep-conductance h(G) vs h(G[B]); does the cut pass through C?
TASK2 vertex connectivity vs |C|.
TASK3 nodal cut V+/V-: fraction of sign-change edges incident to C.
TASK4 energy decomposition lam2 = cut(C,B) + internal-C + internal-B; is internal-B vanishing?
Run: python conjecture_B_final_lemma.py
"""
import numpy as np
import networkx as nx


def fiedler(G, nodelist=None):
    nodes = nodelist if nodelist is not None else list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    ev, V = np.linalg.eigh(L); l2 = ev[1]
    return l2, V[:, 1] / np.linalg.norm(V[:, 1]), nodes


def required_of(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    return l2 * (l2 + S * S / m - fDf), l2, f, nodes, d, A


def carriers(f, nodes, p=0.8):
    order = np.argsort(-(f * f)); cum = np.cumsum((f * f)[order])
    k = min(max(int(np.searchsorted(cum, p)) + 1, 1), len(nodes) - 1)
    return set(nodes[order[i]] for i in range(k))


def block(G, C):
    H = G.subgraph([v for v in G.nodes() if v not in C])
    comps = list(nx.connected_components(H))
    if not comps:
        return None
    cc = max(comps, key=len)
    return list(cc) if len(cc) >= 2 else None


def sweep_conductance(G, f, nodes):
    n = len(nodes); idx = {v: i for i, v in enumerate(nodes)}
    deg = {v: G.degree(v) for v in nodes}; totvol = 2 * G.number_of_edges()
    order = np.argsort(f); inS = [False] * n; volS = 0; cut = 0; best = float('inf')
    for k in range(n - 1):
        i = order[k]; v = nodes[i]; inS[i] = True; volS += deg[v]
        for u in G[v]:
            cut += -1 if inS[idx[u]] else 1
        denom = min(volS, totvol - volS)
        if denom > 0:
            best = min(best, cut / denom)
    return best


def analyze(G):
    Req, l2, f, nodes, d, A = required_of(G)
    if Req <= 1e-9:
        return None
    n = len(nodes); idx = {v: i for i, v in enumerate(nodes)}
    C = carriers(f, nodes); Bn = block(G, C)
    if Bn is None:
        return None
    l2B, fB, _ = fiedler(G.subgraph(Bn), nodelist=Bn)
    ratio = l2B / l2
    hG = sweep_conductance(G, f, nodes)
    HB = G.subgraph(Bn); hB = sweep_conductance(HB, fB, Bn)
    # TASK3 nodal cut + TASK4 energy decomposition
    cut_e = inC_e = inB_e = oth_e = 0.0
    sign_cut_edges = 0; sign_cut_incidentC = 0
    Bset = set(Bn)
    for a, b in G.edges():
        w = (f[idx[a]] - f[idx[b]]) ** 2
        ca, cb = a in C, b in C
        if ca and cb:
            inC_e += w
        elif (not ca) and (not cb):
            if a in Bset and b in Bset:
                inB_e += w
            else:
                oth_e += w
        else:
            cut_e += w
        # nodal sign cut (global Fiedler)
        if (f[idx[a]] >= 0) != (f[idx[b]] >= 0):
            sign_cut_edges += 1
            if ca or cb:
                sign_cut_incidentC += 1
    return dict(Req=Req, l2=l2, l2B=l2B, ratio=ratio, hG=hG, hB=hB,
                hratio=(hB / hG if hG > 1e-12 else float('inf')), nC=len(C), nB=len(Bn),
                cut_e=cut_e, inC_e=inC_e, inB_e=inB_e, oth_e=oth_e,
                frac_inB=inB_e / l2, frac_cut=cut_e / l2,
                sign_frac_C=(sign_cut_incidentC / sign_cut_edges if sign_cut_edges else 1.0),
                n=n, G=G, C=C, Bn=Bn)


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
    out = [("deg2dense", deg2dense(200, 0.65, 2)), ("lollipop", nx.lollipop_graph(50, 10)),
           ("lollipop", nx.lollipop_graph(30, 20)), ("two_cycles", two_cycles(20))]
    rng = np.random.default_rng(7)
    for _ in range(700):
        s = int(rng.integers(0, 2**31)); out.append(
            ("d2d", deg2dense(int(rng.integers(20, 100)), float(rng.uniform(0.3, 0.8)), s)))
    for _ in range(400):
        s = int(rng.integers(0, 2**31)); out.append(("degk", degk_block(
            int(rng.integers(20, 100)), float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 5)), s)))
    for _ in range(300):
        out.append(("lol", nx.lollipop_graph(int(rng.integers(6, 50)), int(rng.integers(2, 25)))))
    for _ in range(300):
        s = int(rng.integers(0, 2**31)); out.append(("pe", pathend_dense(
            int(rng.integers(8, 40)), float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 12)), s)))
    for _ in range(300):
        out.append(("2cyc", two_cycles(int(rng.integers(5, 40)))))
    return out


def main():
    print("TASK 1+3+4 detail on canonical families:")
    print(f"{'fam':10s} {'n':>4} {'lam2':>7} {'ratio':>7} {'h(G)':>7} {'h(B)':>7} "
          f"{'h(B)/h(G)':>9} {'cut%':>6} {'inB%':>6} {'sign_C%':>7}")
    for nm, G in corpus()[:4]:
        a = analyze(G)
        if a:
            print(f"{nm:10s} {a['n']:4d} {a['l2']:7.3f} {a['ratio']:7.1f} {a['hG']:7.3f} "
                  f"{a['hB']:7.3f} {a['hratio']:9.1f} {100*a['frac_cut']:6.1f} "
                  f"{100*a['frac_inB']:6.1f} {100*a['sign_frac_C']:7.1f}")

    print("\nAggregate over Required>0 corpus:")
    A = []
    for nm, G in corpus():
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        a = analyze(G)
        if a:
            A.append(a)
    N = len(A)
    rat = np.array([a['ratio'] for a in A]); hr = np.array([a['hratio'] for a in A])
    fcut = np.array([a['frac_cut'] for a in A]); finB = np.array([a['frac_inB'] for a in A])
    signC = np.array([a['sign_frac_C'] for a in A])
    print(f"N = {N}")
    print(f"  TASK1 h(B)/h(G): min={hr.min():.2f} median={np.median(hr):.2f} "
          f">=2 for {100*np.mean(hr>=2):.1f}%; lam2 ratio min={rat.min():.2f}")
    print(f"  TASK1 corr(h(B)/h(G), lam2-ratio) = {np.corrcoef(hr, rat)[0,1]:.3f}")
    print(f"  TASK3 frac of nodal sign-cut edges incident to C: "
          f"min={signC.min():.2f} median={np.median(signC):.2f} mean={signC.mean():.2f}")
    print(f"        graphs with >=90% sign-cut incident to C: {100*np.mean(signC>=0.9):.1f}%")
    print(f"  TASK4 cut-energy fraction of lam2: median={np.median(fcut):.3f}, "
          f"min={fcut.min():.3f}")
    print(f"  TASK4 internal-B energy fraction of lam2: median={np.median(finB):.4f}, "
          f"max={finB.max():.3f}; <0.1 for {100*np.mean(finB<0.1):.1f}%, "
          f"<0.5 for {100*np.mean(finB<0.5):.1f}%")
    # split by family type via cut fraction
    print(f"  (vertex-bottleneck signature cut%>80: {100*np.mean(fcut>0.8):.1f}% of graphs; "
          f"path-bottleneck inB%>30: {100*np.mean(finB>0.3):.1f}%)")

    print("\nTASK 2: vertex connectivity vs |C| (sample, small graphs)")
    cnt = 0; contains = 0; le = 0
    for a in A:
        if a['n'] > 45 or cnt >= 60:
            continue
        G = a['G']
        try:
            kap = nx.node_connectivity(G)
        except Exception:
            continue
        cnt += 1
        if a['nC'] <= kap:
            le += 1
        # does removing C disconnect G? (C contains a vertex cut iff G-C disconnected or trivial)
        Gc = G.copy(); Gc.remove_nodes_from(a['C'])
        if Gc.number_of_nodes() > 0 and not nx.is_connected(Gc):
            contains += 1
    if cnt:
        print(f"  sampled {cnt}: |C|<=kappa(G) for {100*le/cnt:.0f}%; "
              f"removing C disconnects G for {100*contains/cnt:.0f}% "
              f"(C contains/exceeds a vertex cut)")


if __name__ == "__main__":
    main()
