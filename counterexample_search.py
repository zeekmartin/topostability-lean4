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

if __name__ == "__main__":
    run()
