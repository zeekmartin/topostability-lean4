"""
Conjecture B — what drives α = W/(μ₂·fᵀDf) > 1 (the 15% violators of W ≤ μ₂·fᵀDf)?

μ₂ = normalized-Laplacian Fiedler value; f = combinatorial unit Fiedler;
W = Σ_{ab}(min(d_a,d_b)-δ)(f_a-f_b)²;  R'' = λ₂(fᵀDf-λ₂+1-S²/m).
Recall: μ₂·fᵀDf ≤ R'' on 100%, so proving W ≤ μ₂·fᵀDf would prove B; it fails on ~15%.

Correlates α with 12 graph features, profiles the worst violators, and tests
constant + feature-dependent corrections  W ≤ μ₂·fᵀDf·g.

Run:  python conjecture_B_alpha_analysis.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def sweep_conductance(G, f, nodes):
    """Min conductance over Fiedler sweep cuts (standard proxy)."""
    order = [nodes[i] for i in np.argsort(f)]
    deg = dict(G.degree())
    total_vol = 2 * G.number_of_edges()
    inS = set(); vol = 0; cut = 0; best = 1.0
    for v in order[:-1]:
        inS.add(v); vol += deg[v]
        # update cut: edges from v to outside minus edges from v to inside
        for u in G[v]:
            cut += 1 if u not in inS else -1
        denom = min(vol, total_vol - vol)
        if denom > 0:
            best = min(best, cut / denom)
    return best


def features(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min()); Delta = float(d.max()); dbar = 2.0 * m / n
    S = float(d @ f); fDf = float((d * f * f).sum())
    Rpp = l2 * (fDf - l2 + 1.0 - S * S / m)
    Ln = nx.normalized_laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    mu2 = float(np.linalg.eigvalsh(Ln)[1])
    W = 0.0; SH = 0.0
    eqedges = 0
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        w = min(d[i], d[j]) - delta
        if w > 0:
            W += w * (f[i] - f[j]) ** 2; SH += w
        if d[i] == d[j]:
            eqedges += 1
    alpha = W / (mu2 * fDf) if mu2 * fDf > 1e-12 else 0.0
    # features
    try:
        assort = float(nx.degree_assortativity_coefficient(G))
    except Exception:
        assort = np.nan
    # modularity of Fiedler sign bisection
    Vp = [nodes[i] for i in range(n) if f[i] >= 0]
    Vm = [nodes[i] for i in range(n) if f[i] < 0]
    try:
        mod = float(nx.algorithms.community.modularity(G, [set(Vp), set(Vm)])) \
            if Vp and Vm else 0.0
    except Exception:
        mod = np.nan
    feat = dict(
        clustering=float(nx.average_clustering(G)),
        avgpath=float(nx.average_shortest_path_length(G)),
        sigma2=float(np.var(d)),
        cv2=float(np.var(d)) / dbar**2,
        conductance=sweep_conductance(G, f, nodes),
        l2=l2, mu2=mu2, SH=SH,
        assort=assort, modularity=mod,
        ratio=Delta / delta, density=m / (n * (n - 1) / 2.0),
        freq_eq=eqedges / m,
    )
    return dict(n=n, m=m, W=W, fDf=fDf, mu2=mu2, l2=l2, Rpp=Rpp, SH=SH,
                dbar=dbar, Delta=Delta, delta=delta, alpha=alpha,
                degseq=sorted((int(x) for x in d), reverse=True), feat=feat,
                regular=(Delta == delta))


def hard_set():
    import conjecture_B_proof_v4_explore as v4
    gs = [G for _, G in v4.tight_graphs()]
    gs += [G for _, G in v4.broad_graphs(1500)]
    rng = np.random.default_rng(99); nd = 0
    while nd < 600:
        n = int(rng.integers(8, 14)); p = float(rng.uniform(0.45, 0.95))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if nx.is_connected(G):
            gs.append(G); nd += 1
    for _ in range(800):
        n = int(rng.integers(10, 30)); k = int(rng.integers(4, min(14, n - 1)))
        p = float(rng.uniform(0.05, 0.5))
        gs.append(nx.watts_strogatz_graph(n, k + (k % 2), p, seed=int(rng.integers(0, 2**31))))

    def keep(G):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            return False
        T = ce.triangle_graph(G)
        return T.number_of_nodes() >= 2 and nx.is_connected(T) and ce.lambda2(T) > 1e-6
    return [G for G in gs if keep(G)]


def pear(x, y):
    x = np.asarray(x, float); y = np.asarray(y, float)
    mask = np.isfinite(x) & np.isfinite(y)
    x, y = x[mask], y[mask]
    if len(x) < 3 or np.std(x) < 1e-12 or np.std(y) < 1e-12:
        return np.nan
    return float(np.corrcoef(x, y)[0, 1])


def main():
    rows = [features(G) for G in hard_set()]
    rows = [r for r in rows if not r["regular"] and r["mu2"] > 1e-9 and r["SH"] > 1e-9]
    N = len(rows)
    viol = [r for r in rows if r["alpha"] > 1 + 1e-9]
    nv = len(viol)
    print(f"irregular graphs: {N}   violators (α>1): {nv} ({100*nv/N:.1f}%)")
    print(f"α over all: max={max(r['alpha'] for r in rows):.3f}  "
          f"over violators: median={np.median([r['alpha'] for r in viol]):.3f}")

    keys = list(rows[0]["feat"].keys())
    alpha_all = [r["alpha"] for r in rows]
    alpha_v = [r["alpha"] for r in viol]

    # ---- 1. correlations ----
    print("\n[1] corr(α, feature):       all graphs | violators only")
    corrs = []
    for k in keys:
        ca = pear(alpha_all, [r["feat"][k] for r in rows])
        cv = pear(alpha_v, [r["feat"][k] for r in viol])
        corrs.append((k, ca, cv))
        print(f"   {k:13s}: {ca:+.3f}     | {cv:+.3f}")
    top3 = sorted(corrs, key=lambda t: -abs(t[1] if t[1] == t[1] else 0))[:3]
    print(f"   TOP 3 (|corr| over all): {[t[0] for t in top3]}")

    # ---- 2. constant correction feasibility (separation) ----
    print("\n[2] correction feasibility:")
    Rfrac = np.array([r["Rpp"] / (r["mu2"] * r["fDf"]) for r in rows])
    print(f"   max α = {max(alpha_all):.3f} ; min R''/(μ₂fᵀDf) = {Rfrac.min():.3f}  "
          f"-> constant g {'WORKS' if max(alpha_all) <= Rfrac.min() else 'FAILS (overlap)'}")

    # ---- 3. five worst violators ----
    print("\n[3] five worst violators (full profile):")
    for r in sorted(viol, key=lambda r: -r["alpha"])[:5]:
        ft = r["feat"]
        print(f"   α={r['alpha']:.3f} n={r['n']} m={r['m']} Δ/δ={ft['ratio']:.1f} "
              f"dens={ft['density']:.2f} clust={ft['clustering']:.2f} "
              f"σ²={ft['sigma2']:.2f} cv²={ft['cv2']:.3f} cond={ft['conductance']:.3f} "
              f"assort={ft['assort']:+.2f} mod={ft['modularity']:.2f} "
              f"freq_eq={ft['freq_eq']:.2f} λ₂={r['l2']:.3f} μ₂={r['mu2']:.3f} ΣH={r['SH']:.0f}")
        print(f"      degseq={r['degseq'][:12]}")

    # ---- 4. correction candidates: W ≤ μ₂·fᵀDf·g ----
    print("\n[4] correction candidates  W ≤ μ₂·fᵀDf·g  (and does μ₂·fᵀDf·g ≤ R''?):")
    def test_g(name, gfun):
        okW = 0; okR = 0; both = 0
        for r in rows:
            g = gfun(r)
            base = r["mu2"] * r["fDf"]
            a = r["W"] <= base * g + 1e-7
            b = base * g <= r["Rpp"] + 1e-7
            okW += a; okR += b; both += (a and b)
        print(f"   {name:34s}: W<=base·g {100*okW/N:.0f}% | base·g<=R'' {100*okR/N:.0f}% | "
              f"both {100*both/N:.0f}%")
    test_g("g = 1 + σ²_d/d̄²", lambda r: 1 + r["feat"]["cv2"])
    test_g("g = Δ/d̄", lambda r: r["Delta"] / r["dbar"])
    test_g("g = 1 + assortativity", lambda r: 1 + (r["feat"]["assort"] if r["feat"]["assort"] == r["feat"]["assort"] else 0))
    # data-driven: smallest constant g that fixes W (=max α), check it stays <= R''
    gmax = max(alpha_all)
    test_g(f"g = const {gmax:.2f} (=max α)", lambda r: gmax)
    # combined natural factor
    test_g("g = Δ/δ", lambda r: r["Delta"] / r["delta"])

    main.rows = rows; main.viol = viol


if __name__ == "__main__":
    main()
