"""
Global triangle-gradient anti-correlation as covariance / rearrangement.
Over edges e: t_e=(A²)_ab, g_e=(f_a-f_b)², T=Σ t_e g_e, G=Σ g_e=λ₂, Tau=Σ t_e.
Chebyshev (anti-sorted): T ≤ (Tau/|E|)·G.  Goal: close T ≤ RHS=λ₂(fᵀQf-S²/m).
Run:  python conjecture_B_anticorr_covariance.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def edges_tg(G):
    if not nx.is_connected(G):
        return None
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    if l2 < 1e-9:
        return None
    fDf = float((d * f * f).sum()); S = float(d @ f)
    RHS = l2 * (2 * fDf - l2 - S * S / m)
    Required = l2 * (l2 + S * S / m - fDf)
    A2 = A @ A
    ii, jj = np.triu(A, 1).nonzero()
    t = A2[ii, jj].astype(float)
    g = (f[ii] - f[jj]) ** 2
    T = float((t * g).sum())
    return dict(n=n, m=m, l2=l2, RHS=RHS, Required=Required, T=T, t=t, g=g,
                Tau=float(t.sum()), Deficit=l2 * fDf - T, fDf=fDf)


def corpus_dense(maxn=9, cap=600):
    """corpus, biased to keep denser graphs (more triangles)."""
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        Tg = ce.triangle_graph(G)
        if Tg.number_of_nodes() < 2 or not nx.is_connected(Tg):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=2))
        if key not in seen:
            seen[key] = G.copy()
        if len(seen) >= cap:
            break
    return list(seen.values())


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def families():
    fams = [("corpus", G) for G in corpus_dense(9)]
    for n in (50, 100, 200):
        fams.append(("deg2dense", deg2dense(n, 0.65, 300 + n)))
    for m in (20, 50):
        fams += [("lollipop", nx.lollipop_graph(m, 5)), ("lollipop", nx.lollipop_graph(m, 10))]
    fams += [("circulant", nx.circulant_graph(40, [1, 2])),
             ("circulant", nx.circulant_graph(50, [1, 2, 3])),
             ("ER", nx.gnp_random_graph(60, 0.4, 1)), ("ER", nx.gnp_random_graph(60, 0.6, 2)),
             ("WS", nx.watts_strogatz_graph(60, 8, 0.3, 1))]
    G = nx.complete_graph(15)
    for c in range(1, 3):
        H = nx.relabel_nodes(nx.complete_graph(15), {i: i + c * 15 for i in range(15)})
        G = nx.union(G, H); G.add_edge((c - 1) * 15, c * 15)
    fams.append(("chain", G))
    return fams


def main():
    data = []
    for lab, G in families():
        r = edges_tg(G)
        if r:
            r["label"] = lab; data.append(r)
    print(f"graphs: {len(data)}")

    # ---- TASK 1: covariance diagnostics (per family) ----
    print("\n===== TASK 1: covariance diagnostics (family medians) =====")
    print(f"{'family':11s} {'#':>4} {'corr(t,g)':>9} {'T/(meanT*G)':>12} {'T/RHS':>7} "
          f"{'Def/Req':>8} {'cov<=0%':>8}")
    for lab in ["corpus", "deg2dense", "lollipop", "circulant", "ER", "WS", "chain"]:
        g_ = [r for r in data if r["label"] == lab]
        if not g_:
            continue
        def diag(r):
            t, g = r["t"], r["g"]
            cov = float(np.mean(t * g) - np.mean(t) * np.mean(g))
            corr = float(np.corrcoef(t, g)[0, 1]) if t.std() > 0 and g.std() > 0 else 0.0
            cheb = r["T"] / (np.mean(t) * g.sum()) if g.sum() > 0 else 0.0  # T/((Tau/|E|)·G)
            return cov, corr, cheb, r["T"] / r["RHS"], (r["Deficit"] / r["Required"] if r["Required"] > 1e-9 else np.inf)
        ds = [diag(r) for r in g_]
        med = lambda k: np.median([x[k] for x in ds])
        covneg = np.mean([x[0] <= 1e-12 for x in ds])
        print(f"{lab:11s} {len(g_):4d} {med(1):9.3f} {med(2):12.3f} {med(3):7.3f} "
              f"{med(4) if np.isfinite(med(4)) else -1:8.2f} {100*covneg:7.0f}%")

    # ---- TASK 2: quantile separation (pooled, representative) ----
    print("\n===== TASK 2: quantile overlap (high-t ∩ high-g), pooled per family =====")
    for lab in ["deg2dense", "lollipop", "circulant", "ER"]:
        g_ = [r for r in data if r["label"] == lab]
        worst_overlap = 0.0
        for r in g_:
            t, g = r["t"], r["g"]
            for q in (0.75, 0.90, 0.95, 0.99):
                tt = np.quantile(t, q); gg = np.quantile(g, q)
                hi = (t >= tt) & (g >= gg)
                ov = float((t[hi] * g[hi]).sum()) / (r["T"] + 1e-15)
                worst_overlap = max(worst_overlap, ov if q == 0.90 else 0)
        print(f"  {lab:11s}: max (high-t∩high-g, q90) contribution to T = {worst_overlap:.4f}")
    # detailed for one deg2dense
    r = [r for r in data if r["label"] == "deg2dense"][-1]
    t, g = r["t"], r["g"]
    print(f"  detail deg2dense n={r['n']}: by quantile q (overlap-mass / T):")
    for q in (0.75, 0.90, 0.95, 0.99):
        tt = np.quantile(t, q); gg = np.quantile(g, q)
        hi = (t >= tt) & (g >= gg)
        print(f"     q={q}: |high-t∩high-g|={int(hi.sum())}, overlap T-mass={float((t[hi]*g[hi]).sum())/r['T']:.4f}")

    # ---- TASK 3: candidate global inequalities ----
    print("\n===== TASK 3: candidate bounds (valid upper bound AND ≤ RHS?) =====")
    # (i) Chebyshev T ≤ (Tau/|E|)·λ₂ ; then (Tau/|E|)·λ₂ ≤ RHS ?
    cheb_valid = cheb_closes = 0
    # (ii) threshold split T = Σ_{t≤τ}tg + Σ_{t>τ}tg ≤ τ·λ₂ + (max_{t>τ}g)·Tau
    split_closes = 0
    tot = 0
    worst_cheb = 0.0
    for r in data:
        tot += 1
        t, g = r["t"], r["g"]; l2 = r["l2"]; RHS = r["RHS"]; Tau = r["Tau"]; m = r["m"]
        cheb_bound = (Tau / m) * l2
        if r["T"] <= cheb_bound + 1e-9:
            cheb_valid += 1
        if cheb_bound <= RHS + 1e-9:
            cheb_closes += 1
        worst_cheb = max(worst_cheb, cheb_bound / RHS if RHS > 1e-9 else 0)
        # threshold split at median t
        tau = np.median(t)
        hi = t > tau
        split_bound = tau * l2 + (g[hi].max() if hi.any() else 0.0) * Tau
        # validity: T ≤ split_bound ?  (Σ_{t≤τ}tg ≤ τ Σg=τλ₂; Σ_{t>τ}tg ≤ (max g_hi)Σ_{t>τ}t ≤ g_hi·Tau)
        if r["T"] <= split_bound + 1e-9 and split_bound <= RHS + 1e-9:
            split_closes += 1
    print(f"  (i) Chebyshev T ≤ (Tau/|E|)·λ₂ : valid {cheb_valid}/{tot} (cov≤0) ; "
          f"and (Tau/|E|)·λ₂ ≤ RHS : {cheb_closes}/{tot} ; worst (Tau/|E|)λ₂/RHS={worst_cheb:.1f}")
    print(f"  (ii) threshold split closes (valid AND ≤RHS): {split_closes}/{tot}")

    # ---- TASK 4: structural separator ----
    print("\n===== TASK 4: structural separator (high-t ⇒ low-g  and  high-g ⇒ low-t) =====")
    for lab in ["deg2dense", "lollipop", "circulant", "ER"]:
        g_ = [r for r in data if r["label"] == lab]
        rows = []
        for r in g_:
            t, g = r["t"], r["g"]
            tt90 = np.quantile(t, 0.90); gg90 = np.quantile(g, 0.90)
            # high-t edges: their max g
            maxg_hit = float(g[t >= tt90].max()) if (t >= tt90).any() else 0.0
            # high-g edges: their max t
            maxt_hig = float(t[g >= gg90].max()) if (g >= gg90).any() else 0.0
            rows.append((maxg_hit, gg90, maxt_hig, tt90))
        A = np.array(rows)
        print(f"  {lab:11s}: high-t edges max g={np.median(A[:,0]):.2e} (vs g-q90={np.median(A[:,1]):.2e}); "
              f"high-g edges max t={np.median(A[:,2]):.1f} (vs t-q90={np.median(A[:,3]):.1f})")


if __name__ == "__main__":
    main()
