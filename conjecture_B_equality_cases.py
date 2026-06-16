"""
Conjecture B — study the equality / near-equality cases  λ₂(T(G)) ≈ λ₂(G).

ratio = λ₂(T(G)) / λ₂(G)  ∈ (0,1].  Equality ⇔ ratio ≈ 1.
Over the 45,196-graph corpus (T(G) connected), DEDUPLICATED by isomorphism
(WL hash), classify equality (|ratio-1|<0.001) and near-equality (ratio>0.95).

Run:  python conjecture_B_equality_cases.py
"""
import numpy as np
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
import counterexample_search as ce

TOL = 1e-9
AUTCAP = 60000


def additive_overlap(G):
    """‖P_U ψ_T‖² where U=range(Bᵀ), ψ_T = T(G)-Fiedler. 1 ⇔ T-Fiedler is a lift."""
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    B = np.zeros((n, m))
    for e, (u, v) in enumerate(edges):
        B[idx[u], e] = 1.0; B[idx[v], e] = 1.0
    T = ce.triangle_graph(G)
    LT = nx.laplacian_matrix(T).toarray().astype(float)
    psi = np.linalg.eigh(LT)[1][:, 1]
    P = B.T @ np.linalg.pinv(B @ B.T) @ B
    return float(np.linalg.norm(P @ psi) ** 2)


def aut_size_vt(G):
    n = G.number_of_nodes()
    if G.number_of_edges() == n * (n - 1) // 2:        # complete
        import math
        return math.factorial(n), True
    autos = []
    for i, iso in enumerate(GraphMatcher(G, G).isomorphisms_iter()):
        autos.append(iso)
        if i + 1 >= AUTCAP:
            return f">={AUTCAP}", None
    nodes = list(G.nodes())
    orbit0 = {iso[nodes[0]] for iso in autos}
    return len(autos), (len(orbit0) == n)


def Tiso_johnson(G):
    """Is T(G) isomorphic to the triangular/Johnson graph J(n,2) (= line graph of K_n)?"""
    n = G.number_of_nodes()
    T = ce.triangle_graph(G)
    J = nx.line_graph(nx.complete_graph(n))
    if T.number_of_nodes() != J.number_of_nodes():
        return False
    return (nx.weisfeiler_lehman_graph_hash(T, iterations=4)
            == nx.weisfeiler_lehman_graph_hash(J, iterations=4))


def build_corpus():
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(9):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        l2T = ce.lambda2(T)
        if l2T <= TOL:
            continue
        l2G = ce.lambda2(G)
        ratio = l2T / l2G
        n, m = G.number_of_nodes(), G.number_of_edges()
        key = (n, m, nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = {"G": G.copy(), "n": n, "m": m, "ratio": ratio,
                         "l2G": l2G, "l2T": l2T, "count": 1}
        else:
            seen[key]["count"] += 1
    return list(seen.values())


def classify(rec):
    G = rec["G"]; n = rec["n"]; m = rec["m"]
    rec["complete"] = (m == n * (n - 1) // 2)
    rec["regular"] = ce.is_regular(G)
    rec["tau"] = ce.tauG(G)
    rec["degseq"] = sorted((d for _, d in G.degree()), reverse=True)
    aut, vt = aut_size_vt(G)
    rec["aut"] = aut; rec["vt"] = vt
    rec["Tjohnson"] = Tiso_johnson(G)
    return rec


def main():
    corpus = build_corpus()
    total_distinct = len(corpus)
    total_with_dups = sum(r["count"] for r in corpus)
    print(f"corpus: {total_with_dups} graphs (with sampling dups); "
          f"{total_distinct} DISTINCT up to isomorphism")

    eq = [r for r in corpus if abs(r["ratio"] - 1) < 0.001]
    near95 = [r for r in corpus if r["ratio"] > 0.95]
    print(f"\nEQUALITY (|ratio-1|<0.001): {len(eq)} distinct "
          f"({sum(r['count'] for r in eq)} with dups)")
    print(f"NEAR-EQ (ratio>0.95):      {len(near95)} distinct "
          f"({sum(r['count'] for r in near95)} with dups)")

    for r in eq:
        classify(r)
    for r in near95:
        if "complete" not in r:
            classify(r)

    print("\n=== EQUALITY graphs (all distinct) ===")
    print(f"   {'n':>3s}{'m':>5s}{'ratio':>8s} complete reg  VT   tau  T≅J(n,2)  aut    degseq")
    for r in sorted(eq, key=lambda r: (r["n"], r["m"])):
        print(f"   {r['n']:>3d}{r['m']:>5d}{r['ratio']:>8.5f}  "
              f"{str(r['complete']):>5s} {str(r['regular'])[0]}  {str(r['vt'])[0]}  "
              f"{r['tau']:>4d}  {str(r['Tjohnson']):>5s}  {str(r['aut']):>7s}  {r['degseq']}")
    n_eq_complete = sum(1 for r in eq if r["complete"])
    print(f"\n   of {len(eq)} equality graphs: {n_eq_complete} are complete (K_n), "
          f"{len(eq)-n_eq_complete} non-complete")
    noncomp = [r for r in eq if not r["complete"]]
    if noncomp:
        print("   *** NON-COMPLETE EQUALITY CASES EXIST: ***")
        for r in noncomp:
            print(f"     n={r['n']} m={r['m']} degseq={r['degseq']} reg={r['regular']} "
                  f"vt={r['vt']} ratio={r['ratio']:.5f}")
    else:
        print("   *** equality achieved ONLY by complete graphs K_n in this corpus ***")

    # additive overlap on equality (lift exactness)
    print("\n=== lift exactness (‖P_U ψ_T‖²; 1 ⇔ T-Fiedler is additive) ===")
    ovs = [additive_overlap(r["G"]) for r in eq]
    print(f"   equality graphs: min overlap = {min(ovs):.6f}, all≈1? {all(o>0.999 for o in ovs)}")

    # near-equality structure (ratio 0.95-0.999): the 'approach from below'
    print("\n=== NEAR-EQUALITY from below (0.95 < ratio < 0.999) ===")
    below = sorted([r for r in near95 if r["ratio"] < 0.999], key=lambda r: -r["ratio"])
    print(f"   {len(below)} distinct. Top 15 by ratio (Q=λ₂(G)/λ₂(T)=1/ratio):")
    print(f"   {'n':>3s}{'m':>5s}{'ratio':>8s}{'Q':>7s} complete  #missing(=C(n,2)-m)  degseq")
    for r in below[:15]:
        miss = r["n"] * (r["n"] - 1) // 2 - r["m"]
        if "complete" not in r:
            classify(r)
        print(f"   {r['n']:>3d}{r['m']:>5d}{r['ratio']:>8.5f}{1/r['ratio']:>7.4f}  "
              f"{str(r['complete']):>5s}      {miss:>3d}              {r['degseq']}")
    # how 'almost complete' are they? distribution of missing-edge count
    if below:
        miss_fracs = [(r["n"]*(r["n"]-1)//2 - r["m"]) for r in below]
        print(f"\n   missing-edge count among near-eq-from-below: "
              f"min={min(miss_fracs)} median={int(np.median(miss_fracs))} max={max(miss_fracs)}")
        nc = sum(1 for r in below if not r.get("complete", False))
        print(f"   {nc}/{len(below)} are non-complete (i.e. genuinely below equality)")

    main.corpus = corpus; main.eq = eq; main.near95 = near95


if __name__ == "__main__":
    main()
