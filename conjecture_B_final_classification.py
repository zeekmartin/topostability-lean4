"""
Classify Required>0 graphs by boundary mechanism.
boundary_ratio = (sum_{B-C edges} f_B(v)^2) / (||f_B||^2 * lam2(G)), f_B = Fiedler(G[B]).
TYPE A(tau): boundary_ratio <= tau  -> Courant-Fischer gives lam2(G[B]) >= (1-tau) lam2(G).
TYPE B(tau): boundary_ratio > tau   -> rely on T-smallness (T/RHS<1); check carrier edges
             triangle-poor. Report counts, max T/RHS in B, and whether any graph is neither.
Run: python conjecture_B_final_classification.py
"""
import numpy as np
import networkx as nx


def core(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    Req = l2 * (l2 + S * S / m - fDf)
    RHS = l2 * (2 * fDf - l2 - S * S / m)
    A2 = A @ A
    W = A * A2
    T = float(f @ (np.diag(W @ np.ones(n)) - W) @ f)
    return dict(nodes=nodes, idx={v: i for i, v in enumerate(nodes)}, n=n, L=L, A=A, A2=A2,
                d=d, l2=l2, f=f, Req=Req, RHS=RHS, T=T)


def p80(G, f, nodes, p=0.8):
    order = np.argsort(-(f * f)); cum = np.cumsum((f * f)[order])
    k = min(max(int(np.searchsorted(cum, p)) + 1, 1), len(nodes) - 1)
    C = set(nodes[order[i]] for i in range(k))
    H = G.subgraph([v for v in nodes if v not in C])
    comps = list(nx.connected_components(H))
    if not comps:
        return None, C
    cc = max(comps, key=len)
    return (list(cc) if len(cc) >= 2 else None), C


def analyze(fam, G):
    R = core(G)
    if R['Req'] <= 1e-9:
        return None
    nodes, idx, f, l2 = R['nodes'], R['idx'], R['f'], R['l2']
    Bn, C = p80(G, f, nodes)
    if Bn is None:
        return None
    Bset = set(Bn); H = G.subgraph(Bn)
    LB = nx.laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
    evB, VB = np.linalg.eigh(LB); l2B = float(evB[1]); fB = VB[:, 1] / np.linalg.norm(VB[:, 1])
    lf = {v: fB[i] for i, v in enumerate(Bn)}
    # boundary term = sum over B-C edges of fB(v)^2  (||fB||^2 = 1)
    bnd = 0.0
    for v in Bn:
        for u in G[v]:
            if u not in Bset:
                bnd += lf[v] ** 2
    boundary_ratio = bnd / l2                      # /(||fB||^2 * l2) = /l2
    # T decomposition by edge location + triangle-poorness of carrier-incident edges
    A2 = R['A2']
    T_C = T_bnd = T_blk = T_oth = 0.0
    tsum_carr = 0.0; ncarr = 0
    for a, b in G.edges():
        ia, ib = idx[a], idx[b]
        t = A2[ia, ib]; w = t * (f[ia] - f[ib]) ** 2
        ac, bc = a in C, b in C
        ab_, bb_ = a in Bset, b in Bset
        if ac and bc:
            T_C += w
        elif ac != bc and (ab_ or bb_):
            T_bnd += w
        elif ab_ and bb_:
            T_blk += w
        else:
            T_oth += w
        if ac or bc:                               # carrier-incident edge
            tsum_carr += t; ncarr += 1
    T = R['T']
    return dict(fam=fam, l2=l2, l2B=l2B, ratio=l2B / l2, boundary_ratio=boundary_ratio,
                T=T, RHS=R['RHS'], T_over_RHS=T / R['RHS'] if R['RHS'] > 0 else float('inf'),
                T_over_l2sq=T / l2 ** 2, RHS_over_l2=R['RHS'] / l2,
                T_C=T_C / T if T > 0 else 0, T_bnd=T_bnd / T if T > 0 else 0,
                T_blk=T_blk / T if T > 0 else 0, T_oth=T_oth / T if T > 0 else 0,
                mean_t_carrier=tsum_carr / ncarr if ncarr else 0.0)


# builders
def deg2dense(n, q, s):
    r = np.random.default_rng(s); G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for bb in r.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(bb))
    return G


def degk(n, q, k, s):
    r = np.random.default_rng(s); G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for bb in r.choice(range(1, n), size=min(k, n - 1), replace=False):
        G.add_edge(0, int(bb))
    return G


def two_cycles(Lc):
    G = nx.cycle_graph(Lc); G2 = nx.relabel_nodes(nx.cycle_graph(Lc),
                                                  {i: i + Lc for i in range(Lc)})
    G = nx.union(G, G2); G.add_edge(0, Lc); return G


def pathend(n, q, pl, s):
    r = np.random.default_rng(s); G = nx.gnp_random_graph(n, q, seed=int(r.integers(0, 2**31)))
    at = 0; nx2 = n
    for _ in range(pl):
        G.add_edge(at, nx2); at = nx2; nx2 += 1
    return G


def corpus():
    out = []
    rng = np.random.default_rng(7)
    for _ in range(600):
        out.append(('deg2dense', deg2dense(int(rng.integers(20, 110)), float(rng.uniform(0.3, 0.8)),
                    int(rng.integers(0, 2**31)))))
    for _ in range(400):
        out.append(('degk', degk(int(rng.integers(20, 110)), float(rng.uniform(0.3, 0.8)),
                    int(rng.integers(1, 5)), int(rng.integers(0, 2**31)))))
    for _ in range(400):
        out.append(('lollipop', nx.lollipop_graph(int(rng.integers(6, 55)), int(rng.integers(2, 25)))))
    for _ in range(300):
        out.append(('pathend', pathend(int(rng.integers(8, 40)), float(rng.uniform(0.3, 0.8)),
                    int(rng.integers(1, 12)), int(rng.integers(0, 2**31)))))
    for _ in range(300):
        out.append(('two_cycles', two_cycles(int(rng.integers(5, 40)))))
    return out


def main():
    print("Building corpus + boundary classification...")
    A = []
    for fam, G in corpus():
        if G.number_of_nodes() < 5 or not nx.is_connected(G):
            continue
        a = analyze(fam, G)
        if a:
            A.append(a)
    N = len(A)
    br = np.array([a['boundary_ratio'] for a in A])
    tr = np.array([a['T_over_RHS'] for a in A])
    print(f"N = {N}; B holds (T<=RHS) for {100*np.mean(tr<=1+1e-9):.1f}%; "
          f"max T/RHS = {tr.max():.3f}\n")

    print("Classification by threshold tau (TYPE A: boundary_ratio<=tau; TYPE B: >tau)")
    print(f"{'tau':>5} {'#A':>5} {'#B':>5} {'A: cert ratio>=1-tau':>22} {'B: max T/RHS':>14} "
          f"{'B: med mean_t_carrier':>22}")
    for tau in (0.25, 0.5, 1.0, 2.0):
        Aset = [a for a in A if a['boundary_ratio'] <= tau]
        Bset = [a for a in A if a['boundary_ratio'] > tau]
        # A: does actual ratio >= 1-tau (the certified bound)? and is it positive?
        if Aset and tau < 1:
            okA = np.mean([a['ratio'] >= (1 - tau) - 1e-9 for a in Aset])
            certA = f"{100*okA:5.1f}% (LB={1-tau:.2f})"
        else:
            certA = "n/a (tau>=1)" if tau >= 1 else "n/a"
        maxTR = max((a['T_over_RHS'] for a in Bset), default=0.0)
        medmt = np.median([a['mean_t_carrier'] for a in Bset]) if Bset else 0.0
        print(f"{tau:5.2f} {len(Aset):5d} {len(Bset):5d} {certA:>22} {maxTR:14.3f} {medmt:22.3f}")

    print("\nTYPE B (boundary_ratio > 1) detail -- the path-bottleneck residual:")
    B1 = [a for a in A if a['boundary_ratio'] > 1]
    print(f"  count: {len(B1)}/{N} ({100*len(B1)/N:.1f}%)")
    from collections import Counter
    print(f"  families: {dict(Counter(a['fam'] for a in B1))}")
    if B1:
        trB = np.array([a['T_over_RHS'] for a in B1])
        mtB = np.array([a['mean_t_carrier'] for a in B1])
        print(f"  T/RHS: max={trB.max():.3f} median={np.median(trB):.3f} (B holds: "
              f"{100*np.mean(trB<=1):.1f}%)")
        print(f"  mean_t_carrier (triangles on carrier-incident edges): "
              f"max={mtB.max():.3f} median={np.median(mtB):.3f}; "
              f"==0 for {100*np.mean(mtB<1e-9):.1f}%, <0.5 for {100*np.mean(mtB<0.5):.1f}%")
        tc = np.array([a['T_C'] for a in B1]); tb = np.array([a['T_bnd'] for a in B1])
        tk = np.array([a['T_blk'] for a in B1])
        print(f"  T decomposition (fraction): carrier-internal median={np.median(tc):.3f}, "
              f"boundary median={np.median(tb):.3f}, block-internal median={np.median(tk):.3f}")

    print("\nTYPE A (boundary_ratio < 1) detail -- the vertex-bottleneck majority:")
    A1 = [a for a in A if a['boundary_ratio'] < 1]
    print(f"  count: {len(A1)}/{N} ({100*len(A1)/N:.1f}%); families: "
          f"{dict(Counter(a['fam'] for a in A1))}")
    if A1:
        crt = np.array([a['ratio'] - (1 - a['boundary_ratio']) for a in A1])
        print(f"  actual ratio >= certified (1-boundary_ratio): "
              f"{100*np.mean(crt>=-1e-9):.1f}%; "
              f"median certified LB = {np.median([1-a['boundary_ratio'] for a in A1]):.3f}")

    print("\nNEITHER closed? (boundary_ratio>=1 AND carrier edges NOT triangle-poor "
          "AND T/RHS near 1)")
    neither = [a for a in A if a['boundary_ratio'] >= 1 and a['mean_t_carrier'] >= 0.5
               and a['T_over_RHS'] > 0.9]
    print(f"  graphs in neither-A-nor-B-clean: {len(neither)}")
    overlap = [a for a in A if a['boundary_ratio'] < 1 or a['T_over_RHS'] < 1]
    print(f"  closed by A (boundary<1) OR B (T/RHS<1): {100*len(overlap)/N:.1f}%")


if __name__ == "__main__":
    main()
