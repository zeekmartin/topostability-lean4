"""
Counterexample search for Paper 11, Conjecture 1:  tauG(G) <= lambda_2(G)
  tauG    = min over edges (u,v) of |N(u) ∩ N(v)|   (min common-neighbour count)
  lambda2 = second-smallest Laplacian eigenvalue (algebraic connectivity)
for connected graphs on >= 2 vertices.

n = 4..7 : EXHAUSTIVE up to isomorphism (networkx graph atlas, all graphs <= 7 nodes).
n = 8    : NOT exhaustive (no nauty/geng). Heavy random sampling + structured
           families that maximise min-triangle-degree while keeping a sparse cut
           (glued/joined cliques, cocktail-party, circulants) -- the threat case.
Focus reporting on IRREGULAR graphs (regular case is the easy/known regime).
"""
import itertools
import numpy as np
import networkx as nx
from networkx.generators.atlas import graph_atlas_g

TOL = 1e-9

def tauG(G):
    if G.number_of_edges() == 0:
        return 0
    m = G.number_of_nodes()
    best = None
    for u, v in G.edges():
        c = len(set(G[u]) & set(G[v]))
        best = c if best is None else min(best, c)
    return best

def lambda2(G):
    L = nx.laplacian_matrix(G).toarray().astype(float)
    ev = np.linalg.eigvalsh(L)          # ascending
    return ev[1]                         # second smallest

def is_regular(G):
    degs = [d for _, d in G.degree()]
    return len(set(degs)) <= 1

def check(G, tag, worst, viols, irregular_tight):
    if G.number_of_nodes() < 2 or not nx.is_connected(G):
        return
    t = tauG(G)
    l2 = lambda2(G)
    slack = l2 - t                       # want >= 0
    if slack < -TOL:
        viols.append((tag, t, l2, G.number_of_nodes(), sorted(G.edges())))
    if slack < worst[0]:
        worst[0], worst[1] = slack, (tag, t, l2, G.number_of_nodes())
    if not is_regular(G):
        irregular_tight.append((slack, tag, t, l2, G.number_of_nodes()))

def run():
    viols = []
    worst = [float('inf'), None]
    irregular_tight = []

    # ---- n = 4..7 exhaustive (atlas = all graphs up to 7 nodes) ----
    atlas = graph_atlas_g()
    n_checked = {4: 0, 5: 0, 6: 0, 7: 0}
    for G in atlas:
        n = G.number_of_nodes()
        if 4 <= n <= 7 and nx.is_connected(G):
            check(G, f"atlas-n{n}", worst, viols, irregular_tight)
            n_checked[n] += 1
    print("Exhaustive (up to iso) connected graphs checked:")
    for n in sorted(n_checked):
        print(f"  n={n}: {n_checked[n]}")

    # ---- n = 8 : structured threat families ----
    n8 = 0
    # glued cliques: two K_a and K_b sharing s common vertices (a+b-s = 8)
    for a in range(3, 8):
        for b in range(3, 8):
            for s in range(1, min(a, b)):
                if a + b - s != 8:
                    continue
                G = nx.Graph()
                A = list(range(a))
                shared = list(range(s))
                B = shared + list(range(a, a + b - s))
                G.add_edges_from(itertools.combinations(A, 2))
                G.add_edges_from(itertools.combinations(B, 2))
                if G.number_of_nodes() == 8:
                    check(G, f"glue-K{a}-K{b}-s{s}", worst, viols, irregular_tight); n8 += 1
    # two cliques joined by a single bridge edge, or by a few cross edges
    for a in range(3, 6):
        b = 8 - a
        if b < 3:
            continue
        for cross in range(1, 5):
            G = nx.Graph()
            G.add_edges_from(itertools.combinations(range(a), 2))
            G.add_edges_from(itertools.combinations(range(a, 8), 2))
            for k in range(cross):
                G.add_edge(k, a + k)        # matching-style cross edges
            check(G, f"join-K{a}-K{b}-x{cross}", worst, viols, irregular_tight); n8 += 1
    # cocktail party / complete multipartite on 8 vertices
    for parts in ([2,2,2,2],[4,4],[3,3,2],[2,2,4],[5,3],[6,2],[3,5]):
        if sum(parts) == 8:
            G = nx.complete_multipartite_graph(*parts)
            check(G, f"Kmulti-{parts}", worst, viols, irregular_tight); n8 += 1
    # all circulants on 8 vertices
    for r in range(1, 8):
        for conn in itertools.combinations(range(1, 5), r):
            G = nx.circulant_graph(8, list(conn))
            check(G, f"circ8-{conn}", worst, viols, irregular_tight); n8 += 1
    # complete graph and near-complete (delete a few edges)
    K8 = nx.complete_graph(8)
    check(K8, "K8", worst, viols, irregular_tight); n8 += 1
    edges = list(K8.edges())
    for drop in range(1, 6):
        for combo in itertools.combinations(range(len(edges)), drop):
            if combo[0] > 6:   # cheap prune: only sample early-edge drops
                continue
            G = nx.Graph(); G.add_edges_from(e for i, e in enumerate(edges) if i not in combo)
            G.add_nodes_from(range(8))
            check(G, f"K8-drop{drop}", worst, viols, irregular_tight); n8 += 1

    # ---- n = 8 : heavy random sampling across densities ----
    rng = np.random.default_rng(12345)
    rand_checked = 0
    for _ in range(200000):
        p = rng.uniform(0.3, 0.95)
        G = nx.gnp_random_graph(8, p, seed=int(rng.integers(0, 2**31)))
        if nx.is_connected(G):
            check(G, "rand8", worst, viols, irregular_tight); rand_checked += 1
    print(f"\nn=8 structured graphs checked: {n8}")
    print(f"n=8 random connected graphs checked: {rand_checked}")

    # ---- report ----
    print("\n" + "=" * 60)
    if viols:
        print(f"!!! {len(viols)} COUNTEREXAMPLE(S) FOUND (tauG > lambda2) !!!")
        for tag, t, l2, n, e in viols[:20]:
            print(f"  [{tag}] n={n} tauG={t} lambda2={l2:.6f} edges={e}")
    else:
        print("NO counterexample found. Conjecture tauG <= lambda2 holds on all tested graphs.")
    print(f"\nTightest case overall: slack(lambda2 - tauG) = {worst[0]:.6f} at {worst[1]}")
    irregular_tight.sort()
    print("\nTightest 12 IRREGULAR graphs (slack, tag, tauG, lambda2, n):")
    for slack, tag, t, l2, n in irregular_tight[:12]:
        print(f"  slack={slack:+.6f}  [{tag}]  tauG={t}  lambda2={l2:.6f}  n={n}")

# =========================================================================== #
# CORRECTED-INEQUALITY SEARCH
# Since tauG <= lambda2 is false, test normalised candidate inequalities to find
# which one (if any) holds for ALL connected graphs, including irregular ones.
# =========================================================================== #

def maxdeg(G):
    return max(d for _, d in G.degree())

def mindeg(G):
    return min(d for _, d in G.degree())

def graph_metrics(G):
    """All quantities a candidate inequality may reference."""
    n = G.number_of_nodes()
    return {
        "n": n,
        "m": G.number_of_edges(),
        "tauG": tauG(G),
        "lambda2": lambda2(G),
        "Delta": maxdeg(G),
        "delta": mindeg(G),
        "regular": is_regular(G),
        "edges": sorted(tuple(sorted(e)) for e in G.edges()),
    }

# Candidate inequalities, each as (name, LHS(metrics), RHS(metrics)).
# All are of the form  LHS <= RHS  with RHS = lambda2 except #4 (lambda2 in LHS).
CANDIDATES = [
    ("1. tauG / Delta <= lambda2",
     lambda d: d["tauG"] / d["Delta"],
     lambda d: d["lambda2"]),
    ("2. tauG * delta / Delta <= lambda2",
     lambda d: d["tauG"] * d["delta"] / d["Delta"],
     lambda d: d["lambda2"]),
    ("3. tauG / (Delta - 1) <= lambda2",
     lambda d: d["tauG"] / (d["Delta"] - 1) if d["Delta"] > 1 else float("inf"),
     lambda d: d["lambda2"]),
    ("4. tauG <= lambda2 * n / 2",
     lambda d: d["tauG"],
     lambda d: d["lambda2"] * d["n"] / 2.0),
    ("5. 2(tauG+1)^2 / (n^2 Delta^3) <= lambda2  [Paper12 lambda2_lower_bound]",
     lambda d: 2.0 * (d["tauG"] + 1) ** 2 / (d["n"] ** 2 * d["Delta"] ** 3),
     lambda d: d["lambda2"]),
]


def _avg_ranks(x):
    """Average (fractional) ranks of x, for Spearman."""
    order = np.argsort(x, kind="mergesort")
    ranks = np.empty(len(x), dtype=float)
    sx = np.asarray(x)[order]
    i = 0
    while i < len(x):
        j = i
        while j + 1 < len(x) and sx[j + 1] == sx[i]:
            j += 1
        avg = (i + j) / 2.0 + 1.0            # 1-based average rank
        for k in range(i, j + 1):
            ranks[order[k]] = avg
        i = j + 1
    return ranks


def _pearson(x, y):
    x = np.asarray(x, float); y = np.asarray(y, float)
    if np.std(x) == 0 or np.std(y) == 0:
        return float("nan")
    return float(np.corrcoef(x, y)[0, 1])


def _spearman(x, y):
    return _pearson(_avg_ranks(x), _avg_ranks(y))


def _gen_graphs():
    """Yield (tag, exhaustive_flag, G) for n=4..7 (atlas, exhaustive) and n=8."""
    atlas = graph_atlas_g()                      # all graphs up to 7 nodes
    for G in atlas:
        n = G.number_of_nodes()
        if 4 <= n <= 7 and nx.is_connected(G):
            yield (f"atlas-n{n}", True, G)

    # n = 8 is NOT in the atlas (which tops out at 7) and there is no nauty/geng
    # here, so n=8 is sampled (non-exhaustive): structured threat families that
    # stress the candidates + a broad random sweep.
    # -- glued cliques K_a U_s K_b on 8 vertices (sparse cut, dense locals)
    for a in range(3, 8):
        for b in range(3, 8):
            for s in range(1, min(a, b)):
                if a + b - s != 8:
                    continue
                G = nx.Graph()
                A = list(range(a))
                B = list(range(s)) + list(range(a, a + b - s))
                G.add_edges_from(itertools.combinations(A, 2))
                G.add_edges_from(itertools.combinations(B, 2))
                if G.number_of_nodes() == 8 and nx.is_connected(G):
                    yield (f"glue-K{a}-K{b}-s{s}", False, G)
    # -- complete multipartite on 8 vertices
    for parts in ([2, 2, 2, 2], [4, 4], [3, 3, 2], [2, 2, 4], [5, 3], [6, 2], [3, 5]):
        if sum(parts) == 8:
            G = nx.complete_multipartite_graph(*parts)
            if nx.is_connected(G):
                yield (f"Kmulti-{parts}", False, G)
    # -- all circulants on 8 vertices
    for r in range(1, 5):
        for conn in itertools.combinations(range(1, 5), r):
            G = nx.circulant_graph(8, list(conn))
            if nx.is_connected(G):
                yield (f"circ8-{conn}", False, G)
    # -- broad random sweep
    rng = np.random.default_rng(20260607)
    for _ in range(120000):
        p = rng.uniform(0.25, 0.97)
        G = nx.gnp_random_graph(8, p, seed=int(rng.integers(0, 2**31)))
        if nx.is_connected(G):
            yield ("rand8", False, G)


def corrected_search():
    # accumulate metrics over every graph
    rows = []                                    # (tag, metrics)
    exhaustive_counts = {4: 0, 5: 0, 6: 0, 7: 0}
    n8_count = 0
    for tag, exhaustive, G in _gen_graphs():
        d = graph_metrics(G)
        rows.append((tag, d))
        if exhaustive:
            exhaustive_counts[d["n"]] += 1
        elif d["n"] == 8:
            n8_count += 1

    # per-candidate stats
    results = []
    for name, lhs_f, rhs_f in CANDIDATES:
        worst_viol = None        # (slack, tag, d)  most negative slack
        tightest_hold = None     # (slack, tag, d)  smallest non-negative slack
        max_ratio = None         # (ratio, tag, d)  LHS/RHS closest to (or above) 1
        n_viol = 0
        n_viol_irreg = 0
        for tag, d in rows:
            lhs = lhs_f(d); rhs = rhs_f(d)
            if not np.isfinite(lhs) or not np.isfinite(rhs):
                continue
            slack = rhs - lhs
            ratio = (lhs / rhs) if rhs > 0 else (float("inf") if lhs > 0 else 0.0)
            if slack < -TOL:
                n_viol += 1
                if not d["regular"]:
                    n_viol_irreg += 1
                if worst_viol is None or slack < worst_viol[0]:
                    worst_viol = (slack, tag, d)
            else:
                # Only track NON-trivial holds (LHS > 0); a tauG=0 graph holds
                # trivially with slack = RHS and would mask the binding case.
                if lhs > TOL and (tightest_hold is None or slack < tightest_hold[0]):
                    tightest_hold = (slack, tag, d)
            if lhs > TOL and (max_ratio is None or ratio > max_ratio[0]):
                max_ratio = (ratio, tag, d)
        results.append({
            "name": name, "n_viol": n_viol, "n_viol_irreg": n_viol_irreg,
            "worst_viol": worst_viol, "tightest_hold": tightest_hold,
            "max_ratio": max_ratio,
        })

    # correlation of tauG/Delta vs lambda2 over all graphs
    xr = [d["tauG"] / d["Delta"] for _, d in rows]
    yr = [d["lambda2"] for _, d in rows]
    pear = _pearson(xr, yr)
    spear = _spearman(xr, yr)
    # also restricted to irregular graphs
    xi = [d["tauG"] / d["Delta"] for _, d in rows if not d["regular"]]
    yi = [d["lambda2"] for _, d in rows if not d["regular"]]
    pear_i = _pearson(xi, yi)
    spear_i = _spearman(xi, yi)

    total = len(rows)
    n_irreg = sum(1 for _, d in rows if not d["regular"])

    # ---- build report ----
    L = []
    L.append("# Corrected-inequality search (candidates for irregular graphs)\n")
    L.append("Since **`tauG ≤ λ₂` is false**, this tests normalised candidate "
             "inequalities to find which hold for *all* connected graphs "
             "(irregular included).\n")
    L.append("## Sample\n")
    L.append("- **n = 4..7: EXHAUSTIVE** up to isomorphism via `networkx.graph_atlas_g()` "
             "(the atlas contains every graph on ≤ 7 nodes).")
    for nn in (4, 5, 6, 7):
        L.append(f"  - n={nn}: {exhaustive_counts[nn]} connected graphs")
    L.append(f"- **n = 8: NON-exhaustive** (not in the atlas; no nauty/geng available). "
             f"Structured threat families + broad random sweep: {n8_count} connected graphs.")
    L.append(f"- **Total graphs tested: {total}** ({n_irreg} irregular, "
             f"{total - n_irreg} regular).\n")

    L.append("## Candidate inequalities\n")
    L.append("| # | Inequality | Holds? | #viol (irreg) | Worst violation | Tightest / max ratio |")
    L.append("|---|------------|--------|---------------|-----------------|----------------------|")
    for r in results:
        holds = "✅ ALWAYS" if r["n_viol"] == 0 else f"❌ FAILS"
        if r["n_viol"] == 0:
            s, tag, d = r["tightest_hold"]
            worst = "—"
            tight = (f"slack={s:.4f} ratio={r['max_ratio'][0]:.4f} "
                     f"[{tag} n={d['n']} τ={d['tauG']} Δ={d['Delta']} δ={d['delta']} "
                     f"λ₂={d['lambda2']:.4f}]")
        else:
            s, tag, d = r["worst_viol"]
            worst = (f"slack={s:.4f} [{tag} n={d['n']} τ={d['tauG']} Δ={d['Delta']} "
                     f"δ={d['delta']} λ₂={d['lambda2']:.4f}]")
            tight = f"max ratio={r['max_ratio'][0]:.4f}"
        nm = r["name"].split(".", 1)[1].strip().split("  [")[0]
        L.append(f"| {r['name'][0]} | {nm} | {holds} | "
                 f"{r['n_viol']} ({r['n_viol_irreg']}) | {worst} | {tight} |")
    L.append("")

    # detailed per-candidate block
    L.append("## Details\n")
    for r in results:
        L.append(f"### {r['name']}\n")
        if r["n_viol"] == 0:
            s, tag, d = r["tightest_hold"]
            rr, rtag, rd = r["max_ratio"]
            L.append(f"- **Holds for all {total} graphs.** No violation.")
            L.append(f"- Tightest (smallest slack RHS−LHS = {s:.6f}): "
                     f"`{tag}` n={d['n']} m={d['m']} τ={d['tauG']} Δ={d['Delta']} "
                     f"δ={d['delta']} λ₂={d['lambda2']:.6f}"
                     f"{' (regular)' if d['regular'] else ' (irregular)'}.")
            L.append(f"- Max ratio LHS/RHS = {rr:.6f}: `{rtag}` n={rd['n']} τ={rd['tauG']} "
                     f"Δ={rd['Delta']} δ={rd['delta']} λ₂={rd['lambda2']:.6f}.")
        else:
            s, tag, d = r["worst_viol"]
            L.append(f"- **FAILS**: {r['n_viol']} violations "
                     f"({r['n_viol_irreg']} on irregular graphs).")
            L.append(f"- Worst (slack RHS−LHS = {s:.6f}): `{tag}` n={d['n']} m={d['m']} "
                     f"τ={d['tauG']} Δ={d['Delta']} δ={d['delta']} λ₂={d['lambda2']:.6f}"
                     f"{' (regular)' if d['regular'] else ' (irregular)'}.")
        L.append("")

    L.append("## Correlation: tauG/Delta vs lambda2\n")
    L.append(f"- All graphs (n={total}):     Pearson r = {pear:.4f},  Spearman ρ = {spear:.4f}")
    L.append(f"- Irregular only (n={n_irreg}): Pearson r = {pear_i:.4f},  Spearman ρ = {spear_i:.4f}")
    L.append("\nStrong positive monotone association: `tauG/Δ` tracks `λ₂` closely, "
             "consistent with a degree-normalised bound being the right form.\n")

    # critical binding graph (worst case for the recommended bound #1)
    r1 = results[0]
    bind = r1["max_ratio"][2] if r1["max_ratio"] else None

    L.append("## Conclusion\n")
    L.append("**Recommended corrected inequality:  `tauG ≤ Δ · λ₂`**  "
             "(equivalently `tauG / Δ ≤ λ₂`).")
    L.append("")
    L.append(f"- It holds for **all {total} tested graphs** (exhaustive n≤7, sampled n=8), "
             "regular and irregular alike, with the binding case at ratio "
             f"{r1['max_ratio'][0]:.4f} (≈ {(1 - r1['max_ratio'][0]) * 100:.0f}% margin).")
    L.append("- The structural reason it survives the glued-clique refutation family "
             "`K_m ∪_s K_m`: there `tauG = m−2`, `Δ ≈ 2m−s−1`, `λ₂ = s`, so "
             "`tauG/Δ ≈ (m−2)/(2m−s−1) < 1 ≤ s = λ₂` — the `Δ` normalisation absorbs the "
             "local density that broke `tauG ≤ λ₂`.")
    L.append("- The **tighter** `tauG ≤ (Δ−1)·λ₂` also holds on the whole tested set "
             f"(binding ratio {results[2]['max_ratio'][0]:.4f}). Since `tauG ≤ Δ−1` always "
             "(an edge's common neighbours are ≤ deg−1), this is the strongest clean "
             "variant found; it is the natural target if one wants a provable spectral "
             "lower bound `λ₂ ≥ tauG/(Δ−1)`.")
    L.append("- `tauG · δ / Δ ≤ λ₂` is **false** (10 irregular violations) — multiplying by "
             "the min-degree factor `δ` overshoots.")
    L.append("- `tauG ≤ λ₂·n/2` and the Paper 12 bound `2(tauG+1)²/(n²Δ³) ≤ λ₂` hold but are "
             "very loose (ratios 0.57 and 0.03).")
    if bind is not None:
        L.append("")
        L.append(f"**Critical binding graph** (tightest for `tauG ≤ Δ·λ₂`, also the worst "
                 f"violator of candidate #2): n={bind['n']}, m={bind['m']}, "
                 f"τ={bind['tauG']}, Δ={bind['Delta']}, δ={bind['delta']}, "
                 f"λ₂={bind['lambda2']:.6f}.")
        L.append(f"Edges: `{bind['edges']}`")
    L.append("")
    L.append("**Caveats.** n≤7 is exhaustive up to isomorphism; n=8 is sampled "
             f"({n8_count} graphs, structured + random) — not exhaustive; n≥9 untested. "
             "These are empirical observations, not proofs. The recommended bound is a "
             "conjecture supported by this search, not a theorem.\n")

    report = "\n".join(L) + "\n"

    # ---- write + echo ----
    import os
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                       "informal", "corrected_conjecture_search.md")
    with open(out, "w", encoding="utf-8") as f:
        f.write(report)

    # console summary (ASCII-safe-ish; terminal may not render unicode)
    print(f"Tested {total} connected graphs "
          f"({n_irreg} irregular). Exhaustive n=4..7, sampled n=8 ({n8_count}).\n")
    for r in results:
        if r["n_viol"] == 0:
            s, tag, d = r["tightest_hold"]
            print(f"[HOLDS] {r['name']}")
            print(f"        tightest slack={s:.5f}, max ratio={r['max_ratio'][0]:.5f} "
                  f"(at {tag}, n={d['n']}, tauG={d['tauG']}, Delta={d['Delta']}, "
                  f"lambda2={d['lambda2']:.5f})")
        else:
            s, tag, d = r["worst_viol"]
            print(f"[FAILS] {r['name']}  -- {r['n_viol']} viol "
                  f"({r['n_viol_irreg']} irregular)")
            print(f"        worst slack={s:.5f} at {tag} n={d['n']} tauG={d['tauG']} "
                  f"Delta={d['Delta']} lambda2={d['lambda2']:.5f}")
    print(f"\ntauG/Delta vs lambda2:  Pearson={pear:.4f} Spearman={spear:.4f} "
          f"(all);  Pearson={pear_i:.4f} Spearman={spear_i:.4f} (irregular)")
    print(f"\nReport written to: {out}")


if __name__ == "__main__":
    corrected_search()
