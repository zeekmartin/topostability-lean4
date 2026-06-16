"""
Conjecture B — direct test of the SIGNED Hodge up-vs-down conjecture.

Boundary maps (consistent orientation, vertices ordered, edges i<j, triangles i<j<k):
  B₁: |V|x|E|, edge (u,v): B₁[u]=-1, B₁[v]=+1.
  B₂: |E|x|T|, triangle (a,b,c): ∂[a,b,c]=[b,c]-[a,c]+[a,b] -> +1,-1,+1 on those edges.
  L₁_down = B₁ᵀB₁  (nonzero spec = graph Laplacian nonzero spec, so λ_min⁺ = λ₂(G)).
  L₁_up   = B₂B₂ᵀ.
Test:  r = λ_min⁺(L₁_up) / λ_min⁺(L₁_down)  ≤ 1 ?   (λ_min⁺ = smallest eigenvalue > tol)

Run over: hierarchy graphs (clique complex), deg2+dense, large WS, near-complete,
random ER/BA/WS, and the dim-3 / dim-4 simplicial complexes (using their 2-faces).

Run:  python conjecture_B_hodge_test.py
"""
import numpy as np
import networkx as nx
from itertools import combinations
import counterexample_search as ce

TOL = 1e-7


def hodge(verts, edges, tris):
    """verts: iterable of labels; edges/tris: iterables of frozenset/tuple.
    Returns (lam_min_up, lam2_G, connected, n_tri) or None if no triangles / disc."""
    vlist = list(verts); vmap = {v: i for i, v in enumerate(vlist)}; n = len(vlist)
    elist = sorted(tuple(sorted(e)) for e in edges)
    eidx = {e: i for i, e in enumerate(elist)}; m = len(elist)
    if n < 2 or m < 1:
        return None
    B1 = np.zeros((n, m))
    for e, (u, v) in enumerate(elist):
        B1[vmap[u], e] = -1.0; B1[vmap[v], e] = 1.0
    L0 = B1 @ B1.T
    ev0 = np.linalg.eigvalsh(L0)
    if ev0[1] <= TOL:           # disconnected 1-skeleton
        return None
    lam2 = float(ev0[1])
    tl = [tuple(sorted(t)) for t in tris if len(set(t)) == 3]
    # keep only triangles whose 3 edges are present
    tl = [t for t in tl if (t[0], t[1]) in eidx and (t[0], t[2]) in eidx and (t[1], t[2]) in eidx]
    if not tl:
        return None
    B2 = np.zeros((m, len(tl)))
    for c, (a, b, cc) in enumerate(tl):
        B2[eidx[(b, cc)], c] += 1.0
        B2[eidx[(a, cc)], c] += -1.0
        B2[eidx[(a, b)], c] += 1.0
    L1up = B2 @ B2.T
    evu = np.linalg.eigvalsh(0.5 * (L1up + L1up.T))
    pos = evu[evu > TOL]
    if pos.size == 0:
        return None
    return float(pos[0]), lam2, True, len(tl)


def hodge_graph(G):
    """clique-complex Hodge test for a graph (triangles = 3-cliques)."""
    nodes = list(G.nodes())
    tris = [c for c in combinations(nodes, 3)
            if G.has_edge(c[0], c[1]) and G.has_edge(c[0], c[2]) and G.has_edge(c[1], c[2])]
    return hodge(nodes, [tuple(e) for e in G.edges()], tris)


def run_graphs(gen, label, track, want_unsigned=True, limit=None):
    """gen yields (tag,G). Returns list of records."""
    rows = []
    for i, (tag, G) in enumerate(gen):
        if limit and i >= limit:
            break
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        h = hodge_graph(G)
        if h is None:
            continue
        lup, l2, _, nt = h
        r = lup / l2
        rec = {"label": label, "tag": tag, "n": G.number_of_nodes(),
               "m": G.number_of_edges(), "r": r, "lup": lup, "l2": l2, "ntri": nt}
        if want_unsigned:
            T = ce.triangle_graph(G)
            if T.number_of_nodes() >= 2 and nx.is_connected(T):
                l2T = ce.lambda2(T)
                rec["r_uns"] = (l2T / l2) if l2 > TOL else None
        rows.append(rec)
        track.append(rec)
    return rows


# --------------------------------------------------------------------------- #
def gen_hierarchy():
    for tag, exh, G in ce._gen_graphs_hier(9):
        yield (f"hier-{tag}", G)


def gen_deg2_dense():
    rng = np.random.default_rng(2027)
    for _ in range(400):
        n = int(rng.integers(16, 30)); q = float(rng.uniform(0.55, 0.72))
        Gb = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
        Gb = nx.relabel_nodes(Gb, {i: i + 1 for i in range(n - 1)}); Gb.add_node(0)
        for b in rng.choice(range(1, n), size=2, replace=False):
            Gb.add_edge(0, int(b))
        yield ("deg2+dense", Gb)


def gen_largeWS():
    rng = np.random.default_rng(7)
    for _ in range(400):
        n = int(rng.integers(15, 45)); k = int(rng.integers(6, min(18, n - 1)))
        yield ("WS", nx.watts_strogatz_graph(n, k + (k % 2), float(rng.uniform(0.05, 0.5)),
                                              seed=int(rng.integers(0, 2**31))))


def gen_nearcomplete():
    for n in range(6, 18):
        K = nx.complete_graph(n); E = list(K.edges())
        for k in range(1, 8):
            G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E[k:])
            yield (f"K{n}-{k}e", G)
        G = nx.complete_graph(n)
        for j in range(2, n): G.remove_edge(0, j)
        yield (f"K{n}-star", G)


def gen_randoms():
    rng = np.random.default_rng(99)
    for _ in range(400):
        n = int(rng.integers(8, 25)); p = float(rng.uniform(0.3, 0.9))
        yield ("ER", nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31))))
    for _ in range(300):
        n = int(rng.integers(10, 40)); mm = int(rng.integers(2, 6))
        yield ("BA", nx.barabasi_albert_graph(n, mm, seed=int(rng.integers(0, 2**31))))


def gen_complexes(track):
    """dim-3 and dim-4 simplicial complexes: Hodge test using their 2-faces."""
    import simplicial_T3 as s3
    import simplicial_tower_T4 as s4
    rng = np.random.default_rng(20260608)
    fams = (s3.gen_complete_clique() + s3.gen_spheres(rng)
            + s3.gen_random_complexes(rng, 600))
    rng4 = np.random.default_rng(20260609)
    fams4 = s4.gen_complete_clique4() + s4.gen_random_4complexes(rng4, 400)
    rows = []
    for fam, name, K in fams:
        h = hodge(sorted(K.verts), K.edges, K.tri)
        if h is None:
            continue
        lup, l2, _, nt = h
        rec = {"label": "dim3-complex", "tag": name, "n": len(K.verts),
               "m": len(K.edges), "r": lup / l2, "lup": lup, "l2": l2, "ntri": nt}
        rows.append(rec); track.append(rec)
    for fam, name, K in fams4:
        h = hodge(sorted(K.verts), K.edges, K.tri)
        if h is None:
            continue
        lup, l2, _, nt = h
        rec = {"label": "dim4-complex", "tag": name, "n": len(K.verts),
               "m": len(K.edges), "r": lup / l2, "lup": lup, "l2": l2, "ntri": nt}
        rows.append(rec); track.append(rec)
    return rows


def main():
    allrows = []
    families = [
        ("hierarchy(clique cplx)", gen_hierarchy(), True),
        ("deg2+dense", gen_deg2_dense(), True),
        ("large WS", gen_largeWS(), True),
        ("near-complete", gen_nearcomplete(), True),
        ("random ER/BA", gen_randoms(), True),
    ]
    persum = {}
    for label, gen, uns in families:
        rows = run_graphs(gen, label, allrows, want_unsigned=uns)
        persum[label] = rows
        print(f"{label:26s}: {len(rows):6d} graphs tested")
    # complexes
    crows = gen_complexes(allrows)
    print(f"{'dim3/dim4 complexes':26s}: {len(crows):6d} complexes tested")
    persum["complexes"] = crows

    rs = np.array([x["r"] for x in allrows])
    N = len(allrows)
    viol = [x for x in allrows if x["r"] > 1 + 1e-7]
    print(f"\n=== TOTAL: {N} objects tested ===")
    print(f"VIOLATIONS (r = λ_min⁺(L₁_up)/λ₂(G) > 1): {len(viol)}")
    print(f"r distribution: min={rs.min():.4f}  median={np.median(rs):.4f}  max={rs.max():.4f}")
    print(f"r quantiles: 90%={np.quantile(rs,0.9):.4f} 99%={np.quantile(rs,0.99):.4f} "
          f"99.9%={np.quantile(rs,0.999):.4f}")

    print("\nper-family r (min / median / max ; violations):")
    for label, rows in persum.items():
        if not rows:
            continue
        rr = np.array([x["r"] for x in rows])
        nv = sum(1 for x in rows if x["r"] > 1 + 1e-7)
        print(f"  {label:26s}: {rr.min():.3f} / {np.median(rr):.3f} / {rr.max():.3f}  ; viol={nv}")

    # signed vs unsigned tighter?
    both = [x for x in allrows if x.get("r_uns") is not None]
    tighter = sum(1 for x in both if x["r"] >= x["r_uns"] - 1e-9)
    print(f"\nsigned vs unsigned (over {len(both)} T(G)-connected graphs):")
    print(f"  signed tighter (r_signed ≥ r_unsigned): {tighter}/{len(both)} "
          f"({100*tighter/max(len(both),1):.1f}%)")
    print(f"  median r_signed={np.median([x['r'] for x in both]):.4f}  "
          f"median r_unsigned={np.median([x['r_uns'] for x in both]):.4f}")

    print("\n10 objects with r closest to 1 (from below):")
    le1 = sorted([x for x in allrows if x["r"] <= 1 + 1e-7], key=lambda x: -x["r"])[:10]
    for x in le1:
        print(f"  r={x['r']:.5f}  [{x['label']}] {x['tag']}  n={x['n']} m={x['m']} "
              f"ntri={x['ntri']} λ₂={x['l2']:.4f} λ_min⁺(up)={x['lup']:.4f}")

    main.allrows = allrows


if __name__ == "__main__":
    main()
