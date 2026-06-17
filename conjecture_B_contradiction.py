"""
Proof-by-contradiction test: does a sparse internal cut of B yield a Rayleigh competitor that
violates minimality? Competitor g = Fiedler(G[B]) extended by 0 on C (g _|_ 1), so
R_G(g) = lam2(G[B]) + boundary_term/||g||^2 >= lam2(G) by minimality, i.e.
  lam2(G[B]) >= lam2(G) - boundary_term/||g||^2.
The boundary term INFLATES R_G(g), so the bound is useful only if boundary_term is SMALL.
Also test the cut-indicator competitor of the prompt. Decompose and check by family.
Run: python conjecture_B_contradiction.py
"""
import numpy as np
import networkx as nx


def required_of(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    return l2 * (l2 + S * S / m - fDf), l2, f, nodes, L


def p80_block(G, f, nodes, p=0.8):
    order = np.argsort(-(f * f)); cum = np.cumsum((f * f)[order])
    k = min(max(int(np.searchsorted(cum, p)) + 1, 1), len(nodes) - 1)
    C = set(nodes[order[i]] for i in range(k))
    H = G.subgraph([v for v in nodes if v not in C])
    comps = list(nx.connected_components(H))
    if not comps:
        return None, C
    cc = max(comps, key=len)
    return (list(cc) if len(cc) >= 2 else None), C


def analyze(fam, G):
    Req, l2, f, nodes, L = required_of(G)
    if Req <= 1e-9:
        return None
    n = len(nodes); idx = {v: i for i, v in enumerate(nodes)}
    Bn, C = p80_block(G, f, nodes)
    if Bn is None:
        return None
    Bset = set(Bn); b = len(Bn)
    H = G.subgraph(Bn)
    LB = nx.laplacian_matrix(H, nodelist=Bn).toarray().astype(float)
    evB, VB = np.linalg.eigh(LB); l2B = float(evB[1]); fB = VB[:, 1]
    fB = fB / np.linalg.norm(fB)                       # ||fB||=1 on B

    # ---- competitor 1: B-Fiedler extended by 0 on C ----
    g1 = np.zeros(n)
    for i, v in enumerate(Bn):
        g1[idx[v]] = fB[i]
    # g1 _|_ 1 over V (sum over B is 0 since fB _|_ 1_B)
    g1 = g1 - g1.mean()                                # enforce exactly _|_1
    Rg1 = float(g1 @ L @ g1) / float(g1 @ g1)
    # boundary term = sum over B-C edges of (fB_v)^2 (g=0 on C)
    bdry1 = 0.0
    for v in Bn:
        for u in G[v]:
            if u not in Bset:
                bdry1 += g1[idx[v]] ** 2
    bdry1_rel = bdry1 / float(g1 @ g1)                 # boundary contribution to R

    # ---- competitor 2: cut-indicator from spectral bisection of G[B] ----
    lidx = {v: i for i, v in enumerate(Bn)}
    order = np.argsort(fB)
    deg = LB.diagonal()
    inS = [False] * b; cut = 0; best = (float('inf'), 0)
    for k in range(b - 1):
        i = order[k]; inS[i] = True
        for u in H[Bn[i]]:
            cut += -1 if inS[lidx[u]] else 1
        sz = k + 1; szc = b - sz
        phi = cut / min(sz, szc)
        if phi < best[0]:
            best = (phi, k)
    kcut = best[1]; Sidx = set(order[:kcut + 1].tolist())
    Snodes = set(Bn[i] for i in Sidx); sizeS = len(Snodes); sizeC = b - sizeS
    g2 = np.zeros(n)
    for i, v in enumerate(Bn):
        g2[idx[v]] = (b - sizeS) if v in Snodes else (-sizeS)
    g2 = g2 - g2.mean()
    g2g2 = float(g2 @ g2)
    Rg2 = float(g2 @ L @ g2) / g2g2
    # decompose g2: internal B-cut edges vs B-C boundary edges
    cut_e = bdry_e = 0.0
    for a, c in G.edges():
        ia, ic = idx[a], idx[c]
        w = (g2[ia] - g2[ic]) ** 2
        ab, cb = a in Bset, c in Bset
        if ab and cb:
            if (a in Snodes) != (c in Snodes):
                cut_e += w
        elif ab != cb:
            bdry_e += w
    return dict(fam=fam, l2=l2, l2B=l2B, ratio=l2B / l2, b=b, nC=len(C),
                Rg1=Rg1, Rg1_rel=Rg1 / l2, bdry1_rel=bdry1_rel, bdry1_over_l2=bdry1_rel / l2,
                lemma_rhs=(l2 - bdry1) if False else (l2 - bdry1_rel),  # lam2 - boundary
                Rg2=Rg2, Rg2_rel=Rg2 / l2, cut_rel=cut_e / g2g2, bdry2_rel=bdry_e / g2g2,
                cut_over_l2=cut_e / g2g2 / l2, bdry2_over_l2=bdry_e / g2g2 / l2,
                eBC=count_BC(G, Bset))


def count_BC(G, Bset):
    c = 0
    for a, b in G.edges():
        if (a in Bset) != (b in Bset):
            c += 1
    return c


# builders
def deg2dense(n, q, seed):
    r = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for bb in r.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(bb))
    return G


def degk(n, q, k, seed):
    r = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for bb in r.choice(range(1, n), size=min(k, n - 1), replace=False):
        G.add_edge(0, int(bb))
    return G


def two_cycles(Lc):
    G = nx.cycle_graph(Lc); G2 = nx.relabel_nodes(nx.cycle_graph(Lc),
                                                  {i: i + Lc for i in range(Lc)})
    G = nx.union(G, G2); G.add_edge(0, Lc); return G


def pathend(n, q, pl, seed):
    r = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n, q, seed=int(r.integers(0, 2**31)))
    at = 0; nx2 = n
    for _ in range(pl):
        G.add_edge(at, nx2); at = nx2; nx2 += 1
    return G


def corpus():
    out = [('deg2dense', deg2dense(200, 0.65, 7)), ('deg2dense', deg2dense(80, 0.5, 9)),
           ('lollipop', nx.lollipop_graph(50, 10)), ('lollipop', nx.lollipop_graph(30, 20)),
           ('lollipop', nx.lollipop_graph(20, 5))]
    rng = np.random.default_rng(7)
    for _ in range(500):
        out.append(('deg2dense', deg2dense(int(rng.integers(20, 100)),
                    float(rng.uniform(0.3, 0.8)), int(rng.integers(0, 2**31)))))
    for _ in range(300):
        out.append(('degk', degk(int(rng.integers(20, 100)), float(rng.uniform(0.3, 0.8)),
                    int(rng.integers(1, 5)), int(rng.integers(0, 2**31)))))
    for _ in range(300):
        out.append(('lollipop', nx.lollipop_graph(int(rng.integers(6, 50)),
                    int(rng.integers(2, 25)))))
    for _ in range(200):
        out.append(('pathend', pathend(int(rng.integers(8, 40)), float(rng.uniform(0.3, 0.8)),
                    int(rng.integers(1, 12)), int(rng.integers(0, 2**31)))))
    for _ in range(200):
        out.append(('two_cycles', two_cycles(int(rng.integers(5, 40)))))
    return out


def main():
    print("Building corpus + contradiction competitors...")
    A = []
    for fam, G in corpus():
        if G.number_of_nodes() < 5 or not nx.is_connected(G):
            continue
        a = analyze(fam, G)
        if a:
            A.append(a)
    N = len(A)
    print(f"N = {N}\n")

    print("TASK 1: minimality R(g) >= lam2(G) (sanity) -- competitor 1 (B-Fiedler ext) "
          "and 2 (cut indicator)")
    r1 = np.array([a['Rg1_rel'] for a in A]); r2 = np.array([a['Rg2_rel'] for a in A])
    print(f"  R(g1)/lam2_G: min={r1.min():.3f} median={np.median(r1):.2f} "
          f">=1 for {100*np.mean(r1>=1-1e-6):.1f}%")
    print(f"  R(g2)/lam2_G: min={r2.min():.3f} median={np.median(r2):.2f} "
          f">=1 for {100*np.mean(r2>=1-1e-6):.1f}%")

    print("\nTASK 2: decompose competitor 2 -- cut term vs boundary term (relative to lam2_G)")
    ct = np.array([a['cut_over_l2'] for a in A]); bt = np.array([a['bdry2_over_l2'] for a in A])
    print(f"  cut_term/lam2_G:      min={ct.min():.3f} median={np.median(ct):.2f} "
          f">=1 for {100*np.mean(ct>=1):.1f}%")
    print(f"  boundary_term/lam2_G: min={bt.min():.3f} median={np.median(bt):.2f} "
          f">=1 for {100*np.mean(bt>=1):.1f}%")
    print(f"  KEY: is the CUT term alone >= lam2_G? {100*np.mean(ct>=1):.1f}% "
          f"(if yes, B expands on its own -- boundary not needed)")

    print("\nTASK 3+4: the lemma bound lam2(G[B]) >= lam2(G) - boundary/||g||^2 "
          "(competitor 1)")
    bd = np.array([a['bdry1_over_l2'] for a in A])
    print(f"  boundary1/lam2_G (the deficit in the bound): min={bd.min():.3f} "
          f"median={np.median(bd):.2f} max={bd.max():.2f}")
    print(f"  boundary1 < lam2_G (bound non-vacuous): {100*np.mean(bd<1):.1f}%")
    print(f"  boundary1 < 0.5*lam2_G (bound gives ratio>=0.5): {100*np.mean(bd<0.5):.1f}%")
    print("  => the contradiction proof works only where boundary is small; by family:")
    from collections import defaultdict
    byf = defaultdict(list)
    for a in A:
        byf[a['fam']].append(a['bdry1_over_l2'])
    for fam in sorted(byf):
        v = np.array(byf[fam])
        print(f"    {fam:12s} n={len(v):4d}: boundary1/lam2_G median={np.median(v):6.2f} "
              f"max={v.max():7.2f}; <1 for {100*np.mean(v<1):.0f}%")

    print("\n  Direct check: actual ratio lam2(G[B])/lam2(G) vs the certified lower bound "
          "(1 - boundary1/lam2_G):")
    ar = np.array([a['ratio'] for a in A])
    certified = 1 - bd
    print(f"    actual ratio: min={ar.min():.2f} median={np.median(ar):.2f}")
    print(f"    certified LB (1-boundary): min={certified.min():.2f} "
          f"median={np.median(certified):.2f}; >0 for {100*np.mean(certified>0):.1f}%")
    print(f"    competitor bound proves ratio>=1: NEVER (boundary>0 always) unless boundary=0")


if __name__ == "__main__":
    main()
