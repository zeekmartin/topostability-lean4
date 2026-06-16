"""
Conjecture B — vertex-local decomposition of Δ = λ₂φᵀ(D+A)φ − Σ_c 𝓔_{G[N(c)]}(φ).

Correct vertex split (user's /2 was a typo; φᵀ(D+A)φ = Σ_c φ_c·((D+A)φ)_c):
   Δ_c = λ₂ · φ_c·((D+A)φ)_c − 𝓔_{G[N(c)]}(φ),     Σ_c Δ_c = Δ   (verified).

THE KEY candidate (b) — LOCAL POINCARÉ:
   𝓔_{G[N(c)]}(φ) ≤ λ₂(G) · Σ_{v∈N(c)} φ_v²   for every vertex c.
If true (for the Fiedler φ=f), summing gives Σ_c 𝓔 ≤ λ₂ φᵀDφ ≤ λ₂ φᵀ(D+A)φ
(the last step needs φᵀAφ ≥ 0, i.e. fᵀDf ≥ λ₂, true for NON-complete G), ⇒ B.

Tests Δ_c≥0, (b), degree-weighted split (a), on the corpus + deg2+dense + K_n families.
𝓔_{G[N(c)]}(φ) = Σ_{a,b∈N(c), a~b}(φ_a−φ_b)².

Run:  python conjecture_B_local_decomposition.py
"""
import numpy as np
import networkx as nx
from itertools import combinations
import counterexample_search as ce

TOL = 1e-9


def per_vertex(G, f=None):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    n = len(nodes); m = G.number_of_edges()
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; Q = np.diag(d) + A
    ev, V = np.linalg.eigh(L); l2 = float(ev[1])
    if f is None:
        f = V[:, 1] / np.linalg.norm(V[:, 1])
    Qf = Q @ f
    fAf = float(f @ A @ f)
    recs = []
    for c in nodes:
        ci = idx[c]; Nc = list(G[c])
        Ec = 0.0
        for a, b in combinations(Nc, 2):
            if G.has_edge(a, b):
                Ec += (f[idx[a]] - f[idx[b]]) ** 2
        mass = sum(f[idx[v]] ** 2 for v in Nc)          # Σ_{v∈N(c)} φ_v²
        dc = d[ci]
        delta_c = l2 * f[ci] * Qf[ci] - Ec              # correct split (Σ = Δ)
        delta_c_deg = l2 * (dc / (2 * m)) * float(f @ Q @ f) - Ec   # (a) degree-weighted
        recs.append(dict(c=c, deg=int(dc), fc2=f[ci]**2, Ec=Ec, mass=mass,
                         delta_c=delta_c, delta_c_deg=delta_c_deg,
                         localPoincare=(Ec <= l2 * mass + 1e-9),
                         lp_ratio=(Ec / (l2 * mass) if mass > 1e-12 else 0.0)))
    return dict(n=n, m=m, l2=l2, fAf=fAf, recs=recs,
                complete=(m == n*(n-1)//2),
                Delta=float(l2 * (f @ Q @ f) - sum(r["Ec"] for r in recs)),
                sumDc=sum(r["delta_c"] for r in recs))


def corpus_distinct():
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(9):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def deg2_dense(k=200):
    rng = np.random.default_rng(2027); out = []
    for _ in range(k):
        n = int(rng.integers(16, 30)); q = float(rng.uniform(0.55, 0.72))
        Gb = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
        Gb = nx.relabel_nodes(Gb, {i: i + 1 for i in range(n - 1)}); Gb.add_node(0)
        for b in rng.choice(range(1, n), size=2, replace=False):
            Gb.add_edge(0, int(b))
        if nx.is_connected(Gb):
            T = ce.triangle_graph(Gb)
            if T.number_of_nodes() >= 2 and nx.is_connected(T):
                out.append(Gb)
    return out


def main():
    graphs = corpus_distinct()
    print(f"corpus distinct: {len(graphs)}")
    allrecs = []; vid_err = 0.0
    n_DcPos = n_graph = 0; n_lp_viol_v = 0; n_v = 0
    n_lp_viol_g = 0; n_g_noncomplete = 0
    worst_lp = (0, None)
    for G in graphs:
        q = per_vertex(G)
        vid_err = max(vid_err, abs(q["Delta"] - q["sumDc"]))
        n_graph += 1
        # Delta_c >= 0 ?
        if all(r["delta_c"] >= -1e-7 for r in q["recs"]):
            n_DcPos += 1
        # local Poincare (b)
        for r in q["recs"]:
            n_v += 1
            if not r["localPoincare"]:
                n_lp_viol_v += 1
            if r["lp_ratio"] > worst_lp[0]:
                worst_lp = (r["lp_ratio"], (q["n"], q["m"], r["deg"], q["complete"]))
        if not q["complete"]:
            n_g_noncomplete += 1
            if not all(r["localPoincare"] for r in q["recs"]):
                n_lp_viol_g += 1
        allrecs.append(q)

    print(f"\n[verify] Σ_c Δ_c = Δ : max err {vid_err:.2e}  (correct split confirmed)")
    print(f"\n[Δ_c ≥ 0?] graphs with all Δ_c≥0: {n_DcPos}/{n_graph} "
          f"({100*n_DcPos/n_graph:.1f}%)")

    print(f"\n[(b) LOCAL POINCARÉ  𝓔_{{N(c)}}(f) ≤ λ₂·Σ_{{N(c)}}f²]")
    print(f"   per-vertex violations: {n_lp_viol_v}/{n_v} ({100*n_lp_viol_v/n_v:.2f}%)")
    print(f"   non-complete graphs with ANY violation: {n_lp_viol_g}/{n_g_noncomplete} "
          f"({100*n_lp_viol_g/max(n_g_noncomplete,1):.2f}%)")
    print(f"   worst local ratio 𝓔/(λ₂·mass) = {worst_lp[0]:.4f} at (n,m,deg(c),complete)={worst_lp[1]}")
    print(f"   ⇒ if (b) holds on non-complete G, then B follows (φᵀAφ≥0 there)")

    # deg2+dense lock-breaker family
    print(f"\n[(b) on the deg2+dense lock-breaker family]")
    d2 = deg2_dense(200); vv = 0; tv = 0; gg = 0
    worst2 = 0
    for G in d2:
        q = per_vertex(G); bad = False
        for r in q["recs"]:
            tv += 1
            if not r["localPoincare"]:
                vv += 1; bad = True
            worst2 = max(worst2, r["lp_ratio"])
        if bad:
            gg += 1
    print(f"   {len(d2)} graphs: per-vertex (b) violations {vv}/{tv} ({100*vv/max(tv,1):.2f}%); "
          f"graphs with any violation {gg}/{len(d2)}; worst ratio {worst2:.4f}")

    # K_n, K_n-e, K_n-triangle per-vertex
    print(f"\n[K_n / K_n-e / K_n-△ : per-vertex-type Δ_c and local-Poincaré ratio]")
    for nn in (8, 12):
        for name, builder in [("K_n", lambda: nx.complete_graph(nn)),
                              ("K_n-e", lambda: _rm(nx.complete_graph(nn), [(0,1)])),
                              ("K_n-△", lambda: _rm(nx.complete_graph(nn), [(0,1),(0,2),(1,2)]))]:
            G = builder(); q = per_vertex(G)
            # classify vertices by degree; report Δ_c and lp_ratio by type
            bytype = {}
            for r in q["recs"]:
                bytype.setdefault(r["deg"], []).append(r)
            parts = []
            for dg, rs in sorted(bytype.items()):
                dcs = [r["delta_c"] for r in rs]; lps = [r["lp_ratio"] for r in rs]
                parts.append(f"deg{dg}(×{len(rs)}): Δ_c={np.mean(dcs):+.3f} lpR={np.mean(lps):.3f}")
            print(f"   {name:7s} n={nn}: Δ={q['Delta']:.3f} | " + " | ".join(parts))

    main.allrecs = allrecs


def _rm(G, es):
    G.remove_edges_from(es); return G


if __name__ == "__main__":
    main()
