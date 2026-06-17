"""
Hybrid proof test: gradient bound on equal-degree edges + actual T on unequal-degree.
T = T_eq + T_uneq.  T_eq ≤ T_eq_bound (sharp gradient lemma, valid for equal-degree).
KEY: is T_eq_bound + T_uneq ≤ RHS = λ₂(fᵀQf - S²/m) on ALL graphs?
If yes:  T = T_eq+T_uneq ≤ T_eq_bound+T_uneq ≤ RHS  ⇒ B.
Run:  python conjecture_B_hybrid_test.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def hybrid(G):
    if not nx.is_connected(G):
        return None
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    if l2 < 1e-9:
        return None
    fDf = float((d * f * f).sum()); S = float(d @ f)
    RHS = l2 * (2 * fDf - l2 - S * S / m)
    A2 = A @ A; nbr = {v: set(np.flatnonzero(A[v] > 0.5)) for v in range(n)}; f2 = f * f
    T_eq = T_uneq = T_eq_bound = 0.0
    eq_viol = 0; n_eq = 0; n_uneq = 0
    for i, j in np.argwhere(np.triu(A, 1) > 0.5):
        i, j = int(i), int(j); t = float(A2[i, j]); g2 = (f[i] - f[j]) ** 2
        if d[i] == d[j]:
            n_eq += 1; T_eq += t * g2
            excl = (nbr[i] - nbr[j] - {j}) | (nbr[j] - nbr[i] - {i})
            card = len(excl)
            if card == 0:
                b = 0.0
            else:
                den = (d[i] - l2 + 1) ** 2
                massx = float(sum(f2[u] for u in excl))
                b = card * massx / den if den > 1e-12 else float("inf")
            if g2 > b + 1e-9:
                eq_viol += 1
            T_eq_bound += t * b
        else:
            n_uneq += 1; T_uneq += t * g2
    T = T_eq + T_uneq
    return dict(n=n, m=m, l2=l2, RHS=RHS, T=T, T_eq=T_eq, T_uneq=T_uneq,
                T_eq_bound=T_eq_bound, eq_viol=eq_viol, n_eq=n_eq, n_uneq=n_uneq,
                hybrid=T_eq_bound + T_uneq, Bok=(T <= RHS + 1e-7))


def corpus(maxn=9, cap=1500):
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
    fams = []
    for G in corpus(9):
        fams.append(("corpus", G))
    for n in (50, 100, 200):
        fams.append(("deg2dense", deg2dense(n, 0.65, 300 + n)))
    for m in (20, 50):
        for Lp in (3, 5, 10):
            fams.append(("lollipop", nx.lollipop_graph(m, Lp)))
        for Lp in (3, 5):
            fams.append(("barbell", nx.barbell_graph(m, Lp)))
    # chain of cliques
    for m, k in ((10, 3), (20, 3)):
        G = nx.complete_graph(m)
        for c in range(1, k):
            H = nx.relabel_nodes(nx.complete_graph(m), {i: i + c * m for i in range(m)})
            G = nx.union(G, H); G.add_edge((c - 1) * m, c * m)
        fams.append(("chain", G))
    # appendices
    for m, k, pl in ((20, 5, 3), (30, 5, 5)):
        G = nx.complete_graph(m); nxt = m
        for i in range(k):
            prev = i % m
            for _ in range(pl):
                G.add_edge(prev, nxt); prev = nxt; nxt += 1
        fams.append(("appendix", G))
    # random / regular
    for (nm, G) in [("ER", nx.gnp_random_graph(50, 0.3, seed=1)),
                    ("ER", nx.gnp_random_graph(60, 0.5, seed=2)),
                    ("WS", nx.watts_strogatz_graph(50, 8, 0.3, seed=1)),
                    ("WS", nx.watts_strogatz_graph(60, 6, 0.2, seed=2)),
                    ("Petersen", nx.petersen_graph()),
                    ("circulant", nx.circulant_graph(40, [1, 2])),
                    ("circulant", nx.circulant_graph(50, [1, 2, 3])),
                    ("K_n", nx.complete_graph(12)),
                    ("Kmn", nx.complete_bipartite_graph(5, 7))]:
        fams.append((nm, G))
    return fams


def main():
    rows = []
    for label, G in families():
        r = hybrid(G)
        if r:
            r["label"] = label; rows.append(r)
    print(f"graphs: {len(rows)};  B holds: {sum(r['Bok'] for r in rows)}/{len(rows)}")
    # validity of sharp bound on equal-degree edges
    tot_viol = sum(r["eq_viol"] for r in rows); tot_eq = sum(r["n_eq"] for r in rows)
    print(f"sharp bound valid on equal-degree edges: violations {tot_viol}/{tot_eq}")

    # KEY test: hybrid = T_eq_bound + T_uneq ≤ RHS ?
    viol = [r for r in rows if r["hybrid"] > r["RHS"] + 1e-7]
    print(f"\nKEY TEST  T_eq_bound + T_uneq ≤ RHS:  holds {len(rows)-len(viol)}/{len(rows)}")
    if viol:
        print(f"  *** VIOLATIONS: {len(viol)} graphs where hybrid > RHS ***")
        for r in sorted(viol, key=lambda r: -(r["hybrid"]/r["RHS"]))[:8]:
            print(f"    {r['label']:10s} n={r['n']}: hybrid/RHS={r['hybrid']/r['RHS']:.3f} "
                  f"(T_eq_bound={r['T_eq_bound']:.3f} T_uneq={r['T_uneq']:.3f} RHS={r['RHS']:.3f})")
    else:
        print("  => HYBRID CLOSES B on all tested graphs")
    rr = np.array([r["hybrid"] / r["RHS"] for r in rows if r["RHS"] > 1e-9])
    print(f"  hybrid/RHS: max={rr.max():.3f} median={np.median(rr):.3f}")

    # by family: fractions and ratios
    print("\n===== by family (means) =====")
    print(f"{'family':12s} {'#':>4} {'T_eq/T':>7} {'T_uneq/T':>8} {'Teqbnd/RHS':>11} "
          f"{'hybrid/RHS max':>14}")
    for lab in ["corpus", "deg2dense", "lollipop", "barbell", "chain", "appendix",
                "ER", "WS", "Petersen", "circulant", "K_n", "Kmn"]:
        g = [r for r in rows if r["label"] == lab]
        if not g:
            continue
        teqT = np.mean([r["T_eq"] / r["T"] for r in g if r["T"] > 1e-12])
        tunT = np.mean([r["T_uneq"] / r["T"] for r in g if r["T"] > 1e-12])
        tebR = np.mean([r["T_eq_bound"] / r["RHS"] for r in g if r["RHS"] > 1e-9])
        hmax = max([r["hybrid"] / r["RHS"] for r in g if r["RHS"] > 1e-9], default=0)
        print(f"{lab:12s} {len(g):4d} {teqT:7.3f} {tunT:8.3f} {tebR:11.3f} {hmax:14.3f}")


if __name__ == "__main__":
    main()
