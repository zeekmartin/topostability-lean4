"""
Conjecture B — characterize the complement H of the TIGHT small-A graphs (W/R''>0.7).

G = K_n − H.  λ₂(G)=n−ν_max(L_H), Fiedler(G)=top eigvec f of L_H.
  d_v=(n-1)-deg_H(v),  δ=(n-1)-Δ_H,
  W = Σ_{ab∉H}(Δ_H - max(deg_H a,deg_H b))(f_a-f_b)²,
  R''=(n-ν_max)(A+1-S²/m),  A=-fᵀA_H f-1,  S=-deg_H·f.

Search aggressively for W/R''>0.7 small-A graphs; classify H (star / union-of-stars
/ split / threshold); scan parametric families to find the worst-approaching one.

Run:  python conjecture_B_complement_hard_cases.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce
from itertools import combinations

TOL = 1e-9


def quant(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min()); mult = int(np.sum(np.abs(ev - l2) < 1e-7))
    S = float(d @ f); fDf = float((d * f * f).sum()); A = fDf - l2
    Rpp = l2 * (A + 1 - S * S / m)
    W = 0.0
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        w = min(d[i], d[j]) - delta
        if w > 0:
            W += w * (f[i] - f[j]) ** 2
    return dict(n=n, m=m, l2=l2, A=A, W=W, Rpp=Rpp, mult=mult,
                WR=(W / Rpp if Rpp > 1e-12 else 0.0))


# ---- complement classification ----
def is_threshold(H):
    G = H.copy()
    while G.number_of_nodes() > 0:
        degs = dict(G.degree()); n = G.number_of_nodes()
        v = next((x for x, dd in degs.items() if dd == 0 or dd == n - 1), None)
        if v is None:
            return False
        G.remove_node(v)
    return True


def is_split(H):
    degs = sorted((dd for _, dd in H.degree()), reverse=True)
    n = len(degs)
    mloc = max((i for i in range(1, n + 1) if degs[i - 1] >= i - 1), default=0)
    lhs = sum(degs[:mloc])
    rhs = mloc * (mloc - 1) + sum(degs[mloc:])
    return lhs == rhs


def is_union_of_stars(H):
    for comp in nx.connected_components(H):
        sub = H.subgraph(comp)
        if sub.number_of_nodes() <= 2:
            continue
        hi = sum(1 for _, dd in sub.degree() if dd > 1)
        if hi > 1:                      # a star has exactly one center of degree>1
            return False
    return True


def classify_H(H):
    nz = [dd for _, dd in H.degree() if dd > 0]
    if not nz:
        return "empty", nz
    reg = (max(nz) == min(nz))
    tags = []
    if reg:
        tags.append("support-regular(W=0)")
    if max(nz) == H.number_of_edges() and len(nz) == max(nz) + 1:
        tags.append("star")
    if is_union_of_stars(H):
        tags.append("union-of-stars")
    if is_threshold(H):
        tags.append("threshold")
    if is_split(H):
        tags.append("split")
    return "+".join(tags) if tags else "generic", nz


def H_profile(G):
    H = nx.complement(G); n = G.number_of_nodes()
    nodes = list(G.nodes())
    LH = nx.laplacian_matrix(H, nodelist=nodes).toarray().astype(float)
    evH, VH = np.linalg.eigh(LH); nu = float(evH[-1]); fH = VH[:, -1]
    fH = fH / np.linalg.norm(fH)
    nzdeg = sorted((dd for _, dd in H.degree() if dd > 0), reverse=True)
    pr = (fH @ fH) ** 2 / (np.sum(fH ** 4))     # participation ratio (spread of f)
    cls, nz = classify_H(H)
    supp_reg = (max(nzdeg) - min(nzdeg)) if nzdeg else 0
    return dict(eH=H.number_of_edges(), nu=nu, classes=cls,
                degseqH=nzdeg[:10], suppspread=supp_reg, PR=pr,
                nsupp=len(nzdeg))


# ---- search ----
def search():
    rng = np.random.default_rng(2027); found = []; best = (0, None)
    tested = 0
    for _ in range(20000):
        n = int(rng.integers(8, 22))
        p = float(rng.uniform(0.4, 0.75))       # moderate G -> dense-ish complement
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T) or ce.lambda2(T) <= 1e-6:
            continue
        q = quant(G); tested += 1
        if not (0 < q["A"] < 1.5):
            continue
        if q["WR"] > best[0]:
            best = (q["WR"], G.copy())
        if q["WR"] > 0.7:
            found.append((q, G.copy()))
    return found, best, tested


# ---- parametric families (G = complement of constructed H) ----
def Gcomp(H, n):
    """G = K_n - H on vertex set range(n)."""
    K = nx.complete_graph(n)
    K.remove_edges_from(H.edges())
    return K


def family_scan():
    out = []
    # double star S(p,q): two centers joined, center1 has p leaves, center2 has q leaves
    for (p, q, extra) in [(3, 1, 0), (4, 2, 0), (6, 3, 0), (8, 2, 0), (5, 5, 0)]:
        n = p + q + 2 + 6                       # pad with K_n background
        H = nx.Graph(); c1, c2 = 0, 1; H.add_edge(c1, c2)
        nid = 2
        for _ in range(p): H.add_edge(c1, nid); nid += 1
        for _ in range(q): H.add_edge(c2, nid); nid += 1
        G = Gcomp(H, n)
        if nx.is_connected(G):
            out.append((f"doublestar(p={p},q={q})", quant(G), G))
    # K_a clique-in-H plus t pendant leaves on one clique vertex (irregular dense H)
    for (a, t) in [(3, 2), (4, 3), (5, 4), (6, 4), (4, 6)]:
        n = a + t + 6
        H = nx.complete_graph(a); nid = a
        for _ in range(t): H.add_edge(0, nid); nid += 1
        G = Gcomp(H, n)
        if nx.is_connected(G):
            out.append((f"clique{a}+{t}pend", quant(G), G))
    # threshold graphs via creation sequence (mix of dominating/isolated adds)
    rng = np.random.default_rng(5)
    for trial in range(40):
        n = int(rng.integers(10, 20))
        H = nx.Graph(); H.add_node(0)
        for v in range(1, n):
            H.add_node(v)
            if rng.random() < 0.5:              # dominating add
                for u in range(v): H.add_edge(v, u)
        # use H as complement only if it's not too dense (keep G connected, small-A)
        G = Gcomp(H, n)
        if nx.is_connected(G):
            T = ce.triangle_graph(G)
            if T.number_of_nodes() >= 2 and nx.is_connected(T) and ce.lambda2(T) > 1e-6:
                q = quant(G)
                if 0 < q["A"] < 1.5:
                    out.append((f"threshold-{trial}", q, G))
    # split graphs: clique K_a + independent set I_b, random bipartite links
    for (a, b, pe) in [(4, 6, 0.4), (5, 6, 0.5), (3, 8, 0.5), (6, 6, 0.3)]:
        n = a + b
        H = nx.complete_graph(a)
        H.add_nodes_from(range(a, n))
        for u in range(a):
            for w in range(a, n):
                if rng.random() < pe: H.add_edge(u, w)
        G = Gcomp(H, n)
        if nx.is_connected(G):
            T = ce.triangle_graph(G)
            if T.number_of_nodes() >= 2 and nx.is_connected(T) and ce.lambda2(T) > 1e-6:
                q = quant(G)
                if 0 < q["A"] < 1.5:
                    out.append((f"split(a={a},b={b},p={pe})", q, G))
    return out


def main():
    print("=== searching for W/R'' > 0.7 small-A graphs ===")
    found, best, tested = search()
    print(f"tested {tested} small-A graphs; W/R''>0.7: {len(found)}; "
          f"global max W/R'' = {best[0]:.4f}")
    # characterize the tight ones (top by W/R'')
    found.sort(key=lambda fg: -fg[0]["WR"])
    print("\n--- top tight cases: complement H profile ---")
    print(f"   {'W/R̈':>6s}{'n':>4s}{'A':>6s}{'|H|':>5s}{'ν_max':>7s}{'mult':>5s}"
          f"{'suppΔ':>6s}{'PR':>6s}  H-class / degseqH")
    from collections import Counter
    classcount = Counter()
    for q, G in found[:20]:
        hp = H_profile(G)
        classcount[hp["classes"]] += 1
        print(f"   {q['WR']:>6.3f}{q['n']:>4d}{q['A']:>6.3f}{hp['eH']:>5d}{hp['nu']:>7.2f}"
              f"{q['mult']:>5d}{hp['suppspread']:>6d}{hp['PR']:>6.1f}  "
              f"{hp['classes']}  {hp['degseqH']}")
    print(f"\n   H-class distribution over all {len(found)} tight cases: ", end="")
    allc = Counter(H_profile(G)["classes"] for _, G in found)
    print(dict(allc))
    if best[1] is not None:
        hp = H_profile(best[1]); q = quant(best[1])
        print(f"\n   WORST graph (max W/R''={best[0]:.4f}): n={q['n']} A={q['A']:.3f} "
              f"|H|={hp['eH']} class={hp['classes']} degseqH={hp['degseqH']} suppΔ={hp['suppspread']}")

    print("\n=== parametric families (G = K_n - H) ===")
    fam = family_scan()
    fam.sort(key=lambda x: -x[1]["WR"])
    print(f"   {'family':28s}{'n':>4s}{'A':>7s}{'W':>8s}{'R̈':>8s}{'W/R̈':>7s}  H-class")
    for name, q, G in fam[:25]:
        hp = H_profile(G)
        print(f"   {name:28s}{q['n']:>4d}{q['A']:>7.3f}{q['W']:>8.3f}{q['Rpp']:>8.3f}"
              f"{q['WR']:>7.3f}  {hp['classes']}")

    main.found = found; main.best = best; main.fam = fam


if __name__ == "__main__":
    main()
