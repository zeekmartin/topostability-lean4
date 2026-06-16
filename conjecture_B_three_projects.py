"""
Conjecture B — three focused micro-projects.

P1: stress-test  fᵀDf <= dbar (avg degree)  for the unit Fiedler vector, across
    many graph families. (Worst-case over the whole λ₂-eigenspace, to be robust
    to eigenvalue multiplicity.)
P2: bound D_v+ = Σ_{b~v, d_b>d_v}(f_v-f_b)²  -- test candidate forms (a)-(d),
    find tightest universal C or report the form fails.
P3: what makes the 52 tightest graphs special?  D_v+ at hubs vs leaves; predictors.

Run:  python conjecture_B_three_projects.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


# --------------------------------------------------------------------------- #
def fiedler_data(G):
    """Return (n, m, d, dbar, l2, f, worstFDF) where f is a unit Fiedler vector
    and worstFDF = max fᵀDf over the unit λ₂-eigenspace (multiplicity-robust)."""
    nodes = list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1])
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    # eigenspace of λ₂ (within tol)
    sel = np.abs(ev - l2) < 1e-7
    U2 = V[:, sel]                                  # n x k orthonormal
    M = U2.T @ np.diag(d) @ U2                      # fᵀDf restricted to eigenspace
    worstFDF = float(np.linalg.eigvalsh(M)[-1])     # worst-case fᵀDf over the space
    dbar = 2.0 * m / n
    return n, m, d, dbar, l2, f, worstFDF, int(sel.sum())


# =========================================================================== #
# PROJECT 1 — fᵀDf <= dbar
# =========================================================================== #
def project1():
    rng = np.random.default_rng(1)
    families = {}

    def gen_connected(maker, tries=40):
        for _ in range(tries):
            G = maker()
            if G is not None and G.number_of_nodes() >= 3 and nx.is_connected(G):
                return G
        return None

    fam = {}
    # Erdos-Renyi
    fam["ER"] = []
    for _ in range(1000):
        n = int(rng.integers(10, 101)); p = float(rng.uniform(0.1, 0.9))
        G = gen_connected(lambda: nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31))))
        if G: fam["ER"].append(G)
    # Barabasi-Albert
    fam["BA"] = []
    for _ in range(500):
        n = int(rng.integers(10, 101)); mm = int(rng.integers(2, 6))
        if mm >= n: continue
        G = gen_connected(lambda: nx.barabasi_albert_graph(n, mm, seed=int(rng.integers(0, 2**31))))
        if G: fam["BA"].append(G)
    # Watts-Strogatz
    fam["WS"] = []
    for _ in range(500):
        n = int(rng.integers(10, 101)); k = int(rng.integers(4, 11)); p = float(rng.uniform(0.01, 0.5))
        if k >= n: continue
        G = gen_connected(lambda: nx.watts_strogatz_graph(n, k if k % 2 == 0 else k+1, p,
                                                          seed=int(rng.integers(0, 2**31))))
        if G: fam["WS"].append(G)
    # random regular
    fam["regular"] = []
    for _ in range(500):
        n = int(rng.integers(10, 51)); dd = int(rng.integers(3, max(4, n//2)))
        if (n * dd) % 2 != 0 or dd >= n: continue
        try:
            G = nx.random_regular_graph(dd, n, seed=int(rng.integers(0, 2**31)))
        except Exception:
            continue
        if nx.is_connected(G): fam["regular"].append(G)
    # bipartite random
    fam["bipartite"] = []
    for _ in range(200):
        a = int(rng.integers(5, 26)); b = int(rng.integers(5, 26)); p = float(rng.uniform(0.2, 0.8))
        G = gen_connected(lambda: nx.bipartite.random_graph(a, b, p, seed=int(rng.integers(0, 2**31))))
        if G: fam["bipartite"].append(G)
    # near-Ramanujan: random regular are near-Ramanujan; add explicit d-regular high-girth
    fam["expander~"] = []
    for _ in range(100):
        n = int(rng.integers(20, 51)); dd = int(rng.choice([3, 4, 5, 6]))
        if (n * dd) % 2 != 0 or dd >= n: continue
        try:
            G = nx.random_regular_graph(dd, n, seed=int(rng.integers(0, 2**31)))
        except Exception:
            continue
        if nx.is_connected(G): fam["expander~"].append(G)
    # adversarial: stars, double-stars/brooms, barbells, star+path (high degree variance)
    fam["adversarial"] = []
    adv = []
    for k in range(3, 40):
        adv.append(nx.star_graph(k))                                  # star
        # double broom: two centers + leaves + path between
        for pathlen in (1, 2, 3, 5):
            G = nx.Graph()
            c1, c2 = "c1", "c2"
            for i in range(k): G.add_edge(c1, f"a{i}")
            for i in range(k): G.add_edge(c2, f"b{i}")
            prev = c1
            for j in range(pathlen):
                G.add_edge(prev, f"p{j}"); prev = f"p{j}"
            G.add_edge(prev, c2)
            adv.append(G)
        # barbell: two cliques + path
        for a in (4, 6, 8):
            adv.append(nx.barbell_graph(a, k % 6))
        # star joined to path tail (kite-like)
        G = nx.star_graph(k)
        prev = 0
        for j in range(8):
            G.add_edge(prev, f"t{j}"); prev = f"t{j}"
        adv.append(G)
    for G in adv:
        if G.number_of_nodes() >= 3 and nx.is_connected(G):
            fam["adversarial"].append(G)

    # evaluate
    results = {}
    worst = None  # (ratio, family, n, m)
    total = 0; viol = 0
    for name, gs in fam.items():
        rs = []
        for G in gs:
            n, m, d, dbar, l2, f, worstFDF, mult = fiedler_data(G)
            ratio = worstFDF / dbar
            rs.append(ratio); total += 1
            if worstFDF > dbar + 1e-7:
                viol += 1
            if worst is None or ratio > worst[0]:
                worst = (ratio, name, n, m, mult)
        if rs:
            results[name] = (len(rs), max(rs), float(np.mean(rs)))
    return results, total, viol, worst


# =========================================================================== #
# PROJECT 2 & 3 — D_v+ analysis on T(G)-connected graphs
# =========================================================================== #
def Dplus_data(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes)
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    Dp = np.zeros(n)
    for u in nodes:
        i = idx[u]
        s = 0.0
        for b in G[u]:
            j = idx[b]
            if d[j] > d[i]:
                s += (f[i] - f[j]) ** 2
            elif d[j] == d[i]:
                s += 0.5 * (f[i] - f[j]) ** 2
        Dp[i] = s
    return d, l2, f, Dp


def project23(tight_set, broad_set):
    # ---- P2: candidate bounds, tightest C ----
    # a) D_v+ <= C/d_v       => C_a = max D_v+ * d_v
    # b) D_v+ <= C f_v^2     => C_b = max D_v+ / f_v^2   (inf if D_v+>0, f_v=0)
    # c) D_v+ <= C l2/d_v    => C_c = max D_v+ * d_v / l2
    # d) D_v+ <= (d_v-l2)^2 f_v^2 / d_v  (no free C; test ratio)
    stats = {"a": [], "b_finite": True, "b_break": 0, "c": [], "d": [], "d_break": 0}
    allrows = tight_set + broad_set
    for d, l2, f, Dp in allrows:
        for i in range(len(d)):
            dv = d[i]; dvp = Dp[i]; fv2 = f[i] ** 2
            stats["a"].append(dvp * dv)
            stats["c"].append(dvp * dv / l2 if l2 > 1e-12 else np.nan)
            if fv2 < 1e-10:
                if dvp > 1e-9:
                    stats["b_break"] += 1
                    stats["d_break"] += 1
            else:
                stats["b_finite"] = stats["b_finite"]
                pred_d = (dv - l2) ** 2 * fv2 / dv
                stats["d"].append(dvp / pred_d if pred_d > 1e-12 else np.nan)
    Ca = float(np.nanmax(stats["a"]))
    Cc = float(np.nanmax(stats["c"]))
    Cd = float(np.nanmax([x for x in stats["d"] if x == x]))
    return stats, Ca, Cc, Cd


def hub_leaf(d, Dp):
    n = len(d)
    order = np.argsort(d)
    nq = max(1, n // 4)
    leaves = order[:nq]; hubs = order[-nq:]
    return float(np.mean(Dp[hubs])), float(np.mean(Dp[leaves])), \
        float(np.max(Dp[hubs] * d[hubs]))   # hub-flatness ratio


def main():
    print("=== PROJECT 1: fᵀDf <= dbar (avg degree) ===")
    results, total, viol, worst = project1()
    print(f"total tested: {total}   violations (worst-case over eigenspace): {viol}")
    print(f"{'family':14s} {'count':>6s} {'max ratio':>10s} {'mean ratio':>11s}")
    for name, (cnt, mx, mn) in results.items():
        print(f"{name:14s} {cnt:>6d} {mx:>10.4f} {mn:>11.4f}")
    print(f"closest to violation: ratio={worst[0]:.5f} family={worst[1]} "
          f"n={worst[2]} m={worst[3]} l2-mult={worst[4]}")

    # build T(G)-connected sets for P2/P3 (52 tight + broad), reuse v3/v4 generators
    import conjecture_B_proof_v4_explore as v4
    tightG = [G for _, G in v4.tight_graphs()]
    broadG = [G for _, G in v4.broad_graphs(1800)]
    def keep(G):
        T = ce.triangle_graph(G)
        return T.number_of_nodes() >= 2 and nx.is_connected(T) and ce.lambda2(T) > TOL
    tight_data = [Dplus_data(G) for G in tightG if keep(G)]
    broad_data = [Dplus_data(G) for G in broadG if keep(G)]

    print(f"\n=== PROJECT 2: bounds on D_v+ ({len(tight_data)+len(broad_data)} graphs) ===")
    stats, Ca, Cc, Cd = project23(tight_data, broad_data)
    print(f"(a) D_v+ <= C/d_v        : tightest C = max(D_v+ * d_v)      = {Ca:.4f}  (FINITE -> form OK)")
    print(f"(b) D_v+ <= C·f_v^2      : breaks (D_v+>0 while f_v=0) on {stats['b_break']} vertices "
          f"-> {'NO finite C' if stats['b_break'] else 'finite'}")
    print(f"(c) D_v+ <= C·l2/d_v     : tightest C = max(D_v+ * d_v / l2) = {Cc:.4f}")
    print(f"(d) D_v+ <= (d_v-l2)^2 f_v^2/d_v : breaks on {stats['d_break']} vertices; "
          f"max ratio (where f_v!=0) = {Cd:.4f}  ({'HOLDS C<=1' if Cd<=1+1e-6 else 'ratio>1 -> needs C>1 or fails'})")

    print(f"\n=== PROJECT 3: tight (52) vs broad ===")
    def summ(dataset, label):
        hubs=[]; leaves=[]; flat=[]
        for d, l2, f, Dp in dataset:
            h, le, fr = hub_leaf(d, Dp); hubs.append(h); leaves.append(le); flat.append(fr)
        print(f"{label:8s}: mean D_v+ hubs={np.mean(hubs):.5f}  leaves={np.mean(leaves):.5f}  "
              f"ratio(leaf/hub)={np.mean(leaves)/max(np.mean(hubs),1e-9):.2f}  "
              f"hub-flatness max(D_v+*d) median={np.median(flat):.4f}")
    summ(tight_data, "tight")
    summ(broad_data, "broad")
    main.r1 = (results, total, viol, worst)
    main.r2 = (Ca, Cc, Cd, stats)
    main.tight_data = tight_data; main.broad_data = broad_data


if __name__ == "__main__":
    main()
