"""
Quantify Required vs block-gap; find a regime-split threshold eps.
For all 1962 Required>0 graphs: Required, Deficit, ratio=gamma/lam2 (B=degree-median AND
p=80% Fiedler-complement), Deficit/Required, density/min-degree of the block.
TASK1 Required-vs-ratio boundary; TASK2 split at eps; TASK3 threshold-free products; TASK4 text.
Run: python conjecture_B_final_threshold.py
"""
import numpy as np
import networkx as nx


def analyze(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    A2 = A @ A; W = A * A2
    T = float(f @ (np.diag(W @ np.ones(n)) - W) @ f)
    Required = l2 * (l2 + S * S / m - fDf); Deficit = l2 * fDf - T
    return dict(G=G, nodes=nodes, idx={v: i for i, v in enumerate(nodes)}, n=n, d=d,
                l2=l2, f=f, fDf=fDf, Required=Required, Deficit=Deficit)


def block_lcc(G, Bn):
    H = G.subgraph(Bn)
    comps = list(nx.connected_components(H))
    if not comps:
        return None
    cc = max(comps, key=len)
    return list(cc) if len(cc) >= 2 else None


def gamma_of(G, Bn):
    H = G.subgraph(Bn); LB = nx.laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
    return float(np.linalg.eigvalsh(LB)[1]), float(LB.diagonal().min()), \
        2 * H.number_of_edges() / (len(Bn) * (len(Bn) - 1))


def block_degmed(R):
    nodes, d, n = R['nodes'], R['d'], R['n']
    med = float(np.median(d))
    return block_lcc(R['G'], [nodes[i] for i in range(n) if d[i] >= med])


def block_p80(R, p=0.8):
    nodes, f, n = R['nodes'], R['f'], R['n']
    order = np.argsort(-(f * f)); cum = np.cumsum((f * f)[order])
    k = min(max(int(np.searchsorted(cum, p)) + 1, 1), n - 1)
    C = set(order[:k].tolist())
    return block_lcc(R['G'], [nodes[i] for i in range(n) if i not in C])


# builders (same corpus, seed 7)
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
        out.append(deg2dense(n, 0.65, 100 + n))
    for m in (10, 20, 50):
        for L in (3, 5, 10, 20):
            out.append(nx.lollipop_graph(m, L))
    rng = np.random.default_rng(7)
    for _ in range(900):
        s = int(rng.integers(0, 2**31)); out.append(
            deg2dense(int(rng.integers(20, 120)), float(rng.uniform(0.3, 0.8)), s))
    for _ in range(700):
        s = int(rng.integers(0, 2**31)); out.append(degk_block(
            int(rng.integers(20, 120)), float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 5)), s))
    for _ in range(500):
        out.append(nx.lollipop_graph(int(rng.integers(6, 60)), int(rng.integers(2, 25))))
    for _ in range(500):
        s = int(rng.integers(0, 2**31)); out.append(pathend_dense(
            int(rng.integers(8, 40)), float(rng.uniform(0.3, 0.8)), int(rng.integers(1, 12)), s))
    for _ in range(400):
        out.append(two_cycles(int(rng.integers(5, 40))))
    return out


def main():
    print("Building corpus + block gaps (degree-median and p=80%)...")
    rows = []
    for G in corpus():
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        R = analyze(G)
        if R['Required'] <= 1e-9:
            continue
        Bm = block_degmed(R); Bp = block_p80(R)
        gm = gamma_of(G, Bm) if Bm else (0.0, 0.0, 0.0)
        gp = gamma_of(G, Bp) if Bp else (0.0, 0.0, 0.0)
        rows.append(dict(Req=R['Required'], Def=R['Deficit'], l2=R['l2'],
                         ratio_m=gm[0] / R['l2'], delta_m=gm[1], bm=len(Bm) if Bm else 0,
                         dens_m=gm[2], ratio_p=gp[0] / R['l2'], delta_p=gp[1],
                         bp=len(Bp) if Bp else 0, dens_p=gp[2]))
    A = rows; N = len(A)
    Req = np.array([r['Req'] for r in A]); Def = np.array([r['Def'] for r in A])
    rm = np.array([r['ratio_m'] for r in A]); rp = np.array([r['ratio_p'] for r in A])
    DR = Def / Req
    print(f"N = {N}\n")

    print("TASK 1: Required vs ratio boundary (degree-median block 'm', p=80% block 'p')")
    print(f"  largest Required with ratio_m < 2: {Req[rm<2].max() if (rm<2).any() else 0:.4f}")
    print(f"  smallest Required with ratio_m >= 3: {Req[rm>=3].min():.4f}")
    print(f"  largest Required with ratio_p < 2: {Req[rp<2].max() if (rp<2).any() else 0:.4f}")
    print(f"  smallest Required with ratio_p >= 3: {Req[rp>=3].min():.4f}")
    print("  binned by Required: min/median ratio_m, min/median ratio_p")
    edges = [0, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0, 100]
    for i in range(len(edges) - 1):
        msk = (Req > edges[i]) & (Req <= edges[i + 1])
        if msk.sum() == 0:
            continue
        print(f"    Req in ({edges[i]:.2f},{edges[i+1]:.2f}] n={msk.sum():4d}: "
              f"ratio_m min={rm[msk].min():6.2f} med={np.median(rm[msk]):6.2f} | "
              f"ratio_p min={rp[msk].min():6.2f} med={np.median(rp[msk]):6.2f}")

    print("\nTASK 2: regime split at eps -- below: Deficit margin; above: block gap")
    print(f"{'eps':>6} | {'n<=':>5} {'minDef/Req':>10} {'minDef':>8} {'Def>=eps?':>9} | "
          f"{'n>':>5} {'minRatM':>8} {'minRatP':>8} {'%densP':>7}")
    for eps in (0.01, 0.05, 0.1, 0.5):
        below = Req <= eps; above = ~below
        densP_ok = np.array([r['delta_p'] >= (r['bp'] - 2) / 2 for r in A])
        b_def = Def[below]
        line_below = (f"{below.sum():5d} {DR[below].min():10.2f} {b_def.min():8.4f} "
                      f"{'Y' if b_def.min() >= eps else 'N':>9}")
        if above.sum():
            line_above = (f"{above.sum():5d} {rm[above].min():8.2f} {rp[above].min():8.2f} "
                          f"{100*np.mean(densP_ok[above]):6.1f}%")
        else:
            line_above = f"{0:5d} {'--':>8} {'--':>8} {'--':>7}"
        print(f"{eps:6.2f} | {line_below} | {line_above}")
    # is Deficit>=eps the clean criterion? find the largest eps with (Req<=eps => Def>=Req) trivially true (=B)
    print("  note: Deficit>=Required is just B (always true); the split needs a PROVABLE")
    print("        lower bound on Deficit below eps. Test min Deficit among Req<=eps above.")

    print("\nTASK 3: threshold-free products (want some combo bounded below by c>0)")
    cands = {
        'Required * ratio_m^2': Req * rm**2,
        'Required * ratio_p^2': Req * rp**2,
        'Deficit * ratio_m': Def * rm,
        'Deficit/(Required) [=Def/Req]': DR,
        'Deficit*ratio_p/Required': Def * rp / Req,
        '(Deficit/Required)*(1-1/ratio_p)': DR * (1 - 1 / np.maximum(rp, 1e-9)),
    }
    for name, v in cands.items():
        print(f"  {name:34s}: min={v.min():.4f} median={np.median(v):.3f} "
              f"(>=1 for {100*np.mean(v>=1):.1f}%)")

    print("\nTASK 3b: does a clean monotone Deficit >= h(Required, ratio) emerge?")
    # check Deficit >= Required always (B), and the slack vs ratio
    print(f"  Deficit >= Required (B): {100*np.mean(Def>=Req-1e-12):.1f}%")
    # relative slack (Def-Req)/Req vs ratio_p: is small ratio always paired with large slack?
    slack = (Def - Req) / Req
    lowratio = rp < 2
    print(f"  graphs with ratio_p<2: {lowratio.sum()}; among them min relative slack "
          f"(Def-Req)/Req = {slack[lowratio].min() if lowratio.any() else float('nan'):.2f}, "
          f"max Required = {Req[lowratio].max() if lowratio.any() else 0:.4f}")
    highratio = rp >= 2
    print(f"  graphs with ratio_p>=2: {highratio.sum()}; among them max Required = "
          f"{Req[highratio].max():.4f}, min ratio_p = {rp[highratio].min():.2f}")


if __name__ == "__main__":
    main()
