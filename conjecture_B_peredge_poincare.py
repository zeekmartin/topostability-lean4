"""
Per-edge attack on aggregate Poincare T <= lam2*fDf.
T = sum_{ab in E} t_ab (f_a-f_b)^2,  lam2*fDf = lam2 * sum_{ab in E} (f_a^2 + f_b^2).
Per-edge w_ab = t_ab (f_a-f_b)^2 - lam2 (f_a^2 + f_b^2). Aggregate holds iff sum w_ab <= 0.
Test the CONJECTURE w_ab <= 0 for ALL edges (would trivialize the proof), and characterize.
Run: python conjecture_B_peredge_poincare.py
"""
import numpy as np
import networkx as nx


def edge_w(G):
    nodes = list(G.nodes()); n = len(nodes); idx = {v: i for i, v in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    ws = []
    for a, b in G.edges():
        ia, ib = idx[a], idx[b]
        t = A2[ia, ib]                                  # common neighbours = triangles on edge
        grad = (f[ia] - f[ib]) ** 2
        mass = f[ia] ** 2 + f[ib] ** 2
        w = t * grad - l2 * mass
        ws.append((w, t, grad, mass, f[ia] * f[ib]))
    return l2, ws


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


def corpus():
    out = []
    rng = np.random.default_rng(13)
    for _ in range(150):
        out.append(nx.gnp_random_graph(int(rng.integers(8, 24)), float(rng.uniform(0.3, 0.7)),
                   seed=int(rng.integers(0, 2**31))))
    for _ in range(150):
        out.append(deg2dense(int(rng.integers(20, 80)), float(rng.uniform(0.4, 0.8)),
                   int(rng.integers(0, 2**31))))
    for _ in range(100):
        out.append(degk(int(rng.integers(20, 80)), float(rng.uniform(0.4, 0.8)),
                   int(rng.integers(1, 5)), int(rng.integers(0, 2**31))))
    for _ in range(80):
        out.append(nx.lollipop_graph(int(rng.integers(8, 40)), int(rng.integers(3, 18))))
    for _ in range(60):
        out.append(nx.watts_strogatz_graph(int(rng.integers(15, 30)), 4, 0.3,
                   seed=int(rng.integers(0, 2**31))))
    return out


def main():
    print("Per-edge w_ab = t_ab(f_a-f_b)^2 - lam2(f_a^2+f_b^2) over the corpus...")
    allw = []; pos_frac = []; conj_holds = 0; ngr = 0
    neg_from_t0 = []; tot_neg = []; pos_sum = []; neg_sum = []
    pos_t = []; pos_grad = []; pos_fab = []
    t0_all_neg = 0; t0_edges = 0
    worst_w = -1e9; worst_info = None
    for G in corpus():
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        l2, ws = edge_w(G)
        if not ws:
            continue
        ngr += 1
        w = np.array([x[0] for x in ws])
        allw.extend(w.tolist())
        pos_frac.append(np.mean(w > 1e-12))
        if np.all(w <= 1e-9):
            conj_holds += 1
        ps = w[w > 0].sum(); ns = -w[w < 0].sum()
        pos_sum.append(ps); neg_sum.append(ns)
        # t=0 edges
        tarr = np.array([x[1] for x in ws])
        negmask = w < 0
        neg_t0 = -w[(negmask) & (tarr < 0.5)].sum()
        if ns > 1e-12:
            neg_from_t0.append(neg_t0 / ns)
        t0_edges += int(np.sum(tarr < 0.5))
        t0_all_neg += int(np.sum((tarr < 0.5) & (w <= 1e-9)))
        # positive-edge characterization
        for (wv, t, gr, ms, fab) in ws:
            if wv > 1e-9:
                pos_t.append(t); pos_grad.append(gr); pos_fab.append(fab)
            if wv > worst_w:
                worst_w = wv; worst_info = (t, gr, ms, fab, l2)
    aw = np.array(allw)
    print(f"graphs: {ngr}; total edges: {len(aw)}\n")

    print("7. CONJECTURE w_ab <= 0 for ALL edges:")
    print(f"  graphs where ALL edges have w<=0: {conj_holds}/{ngr} ({100*conj_holds/ngr:.1f}%)")
    print(f"  => conjecture {'HOLDS' if conj_holds==ngr else 'FALSE'} "
          f"(max w over all edges = {aw.max():.4f})")

    print("\n1-2. w_ab distribution:")
    print(f"  fraction of edges with w>0: median over graphs={np.median(pos_frac):.3f}, "
          f"overall={100*np.mean(aw>1e-12):.1f}%")
    print(f"  w: min={aw.min():.3f} median={np.median(aw):.4f} max={aw.max():.4f}")

    print("\n3. positive-w edges - characterization:")
    if pos_t:
        pt = np.array(pos_t); pg = np.array(pos_grad); pf = np.array(pos_fab)
        print(f"  count={len(pt)}; t_ab median={np.median(pt):.1f} (triangle-rich? "
              f"{'yes' if np.median(pt)>1 else 'no'}); grad median={np.median(pg):.4f}; "
              f"f_a*f_b>0 for {100*np.mean(pf>0):.1f}%")
    if worst_info:
        t, gr, ms, fab, l2 = worst_info
        print(f"  worst edge: w={worst_w:.4f} t={t:.0f} grad={gr:.4f} mass={ms:.4f} "
              f"fafb={fab:.4f} lam2={l2:.3f}")

    print("\n4. sum_{w>0} w vs |sum_{w<0} w|:")
    ps = np.array(pos_sum); ns = np.array(neg_sum)
    ratio = ns / np.maximum(ps, 1e-12)
    print(f"  |neg_sum|/pos_sum: min={ratio.min():.2f} median={np.median(ratio):.2f} "
          f"(>1 always = aggregate holds: {100*np.mean(ratio>1):.1f}%)")

    print("\n5. triangle-free (t=0) edges contribute negatively:")
    print(f"  t=0 edges with w<=0: {t0_all_neg}/{t0_edges} ({100*t0_all_neg/max(t0_edges,1):.1f}%)")
    nt0 = np.array(neg_from_t0)
    print(f"  fraction of total NEGATIVE w coming from t=0 edges: "
          f"median={np.median(nt0):.3f} min={nt0.min():.3f} max={nt0.max():.3f}")


if __name__ == "__main__":
    main()
