"""
Nodal hard-edge analysis for the aggregate triangle-Poincare
    T = sum_{ab in E} t_ab (f_a-f_b)^2 <= lam2 * sum_v d_v f_v^2 = lam2 fDf.

Per-edge w_ab = t_ab (f_a-f_b)^2 - lam2 (f_a^2 + f_b^2);  aggregate holds iff sum w_ab <= 0.

Hard edges H = { ab : t_ab >= lam2  AND  f_a*f_b < 0 }  (nodal boundary, triangle-rich).

Hub-flatness lemma (Paper14): for a Fiedler vector of unit norm,
    f_v^2 <= d_v / (d_v - lam2)^2     (valid when d_v > lam2).

TASK 1 : are hard-edge endpoints small (|f|, mass, degree)?
TASK 2 : is the smallness explained by degree (hub-flatness tightness)?
TASK 3 : PosHard / NegEasy ratio.
TASK 4 : candidate hub-flatness bound  HardBound = sum_H (2t-lam2)*[hubsum]  vs NegEasy.
TASK 5 : if HardBound fails, diagnose why.

Run: python conjecture_B_nodal_hard_edges.py
"""
import numpy as np
import networkx as nx


# ---------------------------------------------------------------- per-edge data
def edge_data(G):
    """Return lam2 and a list of per-edge dicts with everything tasks 1-5 need."""
    nodes = list(G.nodes()); idx = {v: i for i, v in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])          # unit-norm Fiedler vector
    A2 = A @ A
    edges = []
    for a, b in G.edges():
        ia, ib = idx[a], idx[b]
        t = A2[ia, ib]                              # common neighbours = triangles on edge
        fa, fb = f[ia], f[ib]
        da, db = d[ia], d[ib]
        grad = (fa - fb) ** 2
        mass = fa ** 2 + fb ** 2
        w = t * grad - l2 * mass
        edges.append(dict(t=t, fa=fa, fb=fb, da=da, db=db,
                          grad=grad, mass=mass, w=w, fafb=fa * fb))
    return l2, edges


def hub_flat(d, l2):
    """Hub-flatness bound on f_v^2; np.inf when d <= lam2 (bound vacuous)."""
    gap = d - l2
    return np.where(gap > 1e-9, d / np.maximum(gap, 1e-12) ** 2, np.inf)


# ---------------------------------------------------------------- graph builders
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


# ---------------------------------------------------------------- main analysis
def main():
    graphs = corpus()
    # accumulators across all hard edges (tasks 1-2)
    h_maxabs = []       # max(|f_a|,|f_b|) per hard edge
    h_mass = []         # f_a^2+f_b^2 per hard edge
    h_da, h_db = [], []
    h_t_over_mindeg = []
    h_hubsum = []       # hub-flatness bound on f_a^2+f_b^2
    h_tight = []        # actual mass / hubsum
    h_fv2_vs_bound = [] # per-endpoint actual f_v^2 / hubflat(d_v)  (the two endpoints)
    n_hard = 0
    n_hard_degok = 0    # hard edges where BOTH endpoints have d_v > lam2 (hub-flatness usable)

    # per-graph accumulators (tasks 3-4)
    pos_over_neg = []   # PosHard / NegEasy
    bound_over_neg = [] # HardBound / NegEasy
    hardbound_ok = 0
    n_graphs = 0
    n_graphs_with_hard = 0
    worst_bound_ratio = -1.0
    worst_bound_info = None

    for G in graphs:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        l2, edges = edge_data(G)
        if not edges or l2 < 1e-9:
            continue
        n_graphs += 1

        # classify edges
        H = [e for e in edges if e['t'] >= l2 - 1e-12 and e['fafb'] < 0]
        easy = [e for e in edges if not (e['t'] >= l2 - 1e-12 and e['fafb'] < 0)]

        # Task 3: PosHard (positive w on hard edges) and NegEasy (negative w on easy edges)
        PosHard = sum(e['w'] for e in H if e['w'] > 0)
        NegEasy = -sum(e['w'] for e in easy if e['w'] < 0)
        if NegEasy > 1e-12:
            pos_over_neg.append(PosHard / NegEasy)

        # Task 4: candidate hub-flatness bound on the hard mass
        HardBound = 0.0
        for e in H:
            hubsum = hub_flat(e['da'], l2) + hub_flat(e['db'], l2)
            HardBound += (2 * e['t'] - l2) * hubsum
        if NegEasy > 1e-12:
            r = HardBound / NegEasy
            bound_over_neg.append(r)
            if np.isfinite(r) and r > worst_bound_ratio:
                worst_bound_ratio = r
                worst_bound_info = (G.number_of_nodes(), G.number_of_edges(),
                                    len(H), l2, HardBound, NegEasy)
        if H:
            n_graphs_with_hard += 1
            # HardBound <= NegEasy ?
            if np.isfinite(HardBound) and HardBound <= NegEasy + 1e-12:
                hardbound_ok += 1

        # Tasks 1-2: per-hard-edge statistics
        for e in H:
            n_hard += 1
            h_maxabs.append(max(abs(e['fa']), abs(e['fb'])))
            h_mass.append(e['mass'])
            h_da.append(e['da']); h_db.append(e['db'])
            h_t_over_mindeg.append(e['t'] / min(e['da'], e['db']))
            hb_a = hub_flat(e['da'], l2); hb_b = hub_flat(e['db'], l2)
            hubsum = hb_a + hb_b
            h_hubsum.append(hubsum)
            if np.isfinite(hubsum) and hubsum > 1e-12:
                h_tight.append(e['mass'] / hubsum)
            if np.isfinite(hb_a):
                h_fv2_vs_bound.append(e['fa'] ** 2 / hb_a)
            if np.isfinite(hb_b):
                h_fv2_vs_bound.append(e['fb'] ** 2 / hb_b)
            if np.isfinite(hb_a) and np.isfinite(hb_b):
                n_hard_degok += 1

    # ------------------------------------------------------------ report
    def stat(name, arr, fmt="{:.4f}"):
        a = np.array([x for x in arr if np.isfinite(x)])
        if len(a) == 0:
            print(f"  {name}: (none)")
            return
        print(f"  {name}: min={fmt.format(a.min())} median={fmt.format(np.median(a))} "
              f"max={fmt.format(a.max())} mean={fmt.format(a.mean())}")

    print("=" * 70)
    print(f"graphs analysed: {n_graphs};  graphs with >=1 hard edge: {n_graphs_with_hard}")
    print(f"total hard edges H = {{t>=lam2 and f_a f_b<0}}: {n_hard}")
    print(f"hard edges where BOTH endpoints have d_v > lam2 (hub-flat usable): "
          f"{n_hard_degok}/{n_hard} ({100*n_hard_degok/max(n_hard,1):.1f}%)")

    print("\n--- TASK 1: are hard-edge endpoints small? ---")
    stat("max(|f_a|,|f_b|)", h_maxabs)
    stat("mass f_a^2+f_b^2 ", h_mass)
    stat("d_a (hard edges) ", h_da, "{:.1f}")
    stat("d_b (hard edges) ", h_db, "{:.1f}")
    print("  -> per-endpoint actual f_v^2 / hub-flat(d_v):")
    stat("    f_v^2 / bound ", h_fv2_vs_bound)

    print("\n--- TASK 2: is smallness explained by degree? ---")
    stat("t_ab / min(d_a,d_b)        ", h_t_over_mindeg)
    stat("hub-flat sum on mass       ", h_hubsum)
    stat("actual mass / hub-flat sum ", h_tight)

    print("\n--- TASK 3: total hard positive mass vs easy negative reservoir ---")
    pon = np.array(pos_over_neg)
    print(f"  PosHard/NegEasy over {len(pon)} graphs: "
          f"max={pon.max():.4f} median={np.median(pon):.4f} mean={pon.mean():.4f}")
    print(f"  fraction of graphs with PosHard < NegEasy: {100*np.mean(pon < 1):.1f}%")

    print("\n--- TASK 4: candidate hub-flatness bound HardBound vs NegEasy ---")
    bon = np.array([x for x in bound_over_neg if np.isfinite(x)])
    n_inf = sum(1 for x in bound_over_neg if not np.isfinite(x))
    print(f"  HardBound <= NegEasy holds: {hardbound_ok}/{n_graphs_with_hard} graphs "
          f"({100*hardbound_ok/max(n_graphs_with_hard,1):.1f}%)")
    if len(bon):
        print(f"  HardBound/NegEasy (finite): max={bon.max():.3f} median={np.median(bon):.3f} "
              f"mean={bon.mean():.3f}")
    print(f"  graphs where HardBound = +inf (an endpoint has d_v <= lam2): {n_inf}")
    if worst_bound_info:
        n, m, nh, l2, hb, ne = worst_bound_info
        print(f"  worst finite ratio={worst_bound_ratio:.3f}: n={n} m={m} |H|={nh} "
              f"lam2={l2:.3f} HardBound={hb:.4f} NegEasy={ne:.4f}")

    print("\n--- TASK 5: diagnosis (computed from above) ---")
    # degree high enough?
    tmd = np.array(h_t_over_mindeg)
    print(f"  t_ab/min(deg): median={np.median(tmd):.3f} -> "
          f"{'edges are near-degree (high-degree endpoints)' if np.median(tmd)>0.4 else 't well below degree'}")
    # hub-flatness tightness
    ht = np.array([x for x in h_tight if np.isfinite(x)])
    print(f"  hub-flat tightness mass/bound: median={np.median(ht):.4f} -> "
          f"{'LOOSE (bound >> actual)' if np.median(ht)<0.2 else 'reasonable'}")
    print(f"  PosHard/NegEasy max={pon.max():.3f} -> true per-graph margin "
          f"{'always < 1 (reservoir suffices)' if pon.max()<1 else 'CAN EXCEED 1'}")
    print(f"  HardBound success rate {100*hardbound_ok/max(n_graphs_with_hard,1):.1f}% "
          f"and inf-count {n_inf} indicate whether the bound is viable.")
    print("=" * 70)

    return dict(n_graphs=n_graphs, n_graphs_with_hard=n_graphs_with_hard, n_hard=n_hard,
                n_hard_degok=n_hard_degok, pon=pon, bon=bon, n_inf=n_inf,
                hardbound_ok=hardbound_ok, worst_bound=worst_bound_info,
                h_maxabs=np.array(h_maxabs), h_mass=np.array(h_mass),
                h_da=np.array(h_da), h_db=np.array(h_db),
                h_tmd=tmd, h_tight=ht, h_fv2=np.array(h_fv2_vs_bound))


if __name__ == "__main__":
    main()
