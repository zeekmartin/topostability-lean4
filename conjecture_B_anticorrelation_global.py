"""
Global triangle-gradient anti-correlation on Required>0 families.
T = Σ_ab t_ab (f_a-f_b)².  RHS = λ₂(fᵀQf - S²/m).
Per-edge gradient bound (Paper14, adjacent): (f_a-f_b)² ≤ |N(a)△N(b)|/(min(d_a,d_b)-λ₂+1)².
T_bound = Σ_ab t_ab·|N(a)△N(b)|/(min(d_a,d_b)-λ₂+1)².
Run:  python conjecture_B_anticorrelation_global.py
"""
import numpy as np
import networkx as nx


def quant(G, name):
    if not nx.is_connected(G):
        return None
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    RHS = l2 * (2 * fDf - l2 - S * S / m)
    Required = l2 * (l2 + S * S / m - fDf)
    A2 = A @ A
    nbr = {v: set(np.flatnonzero(A[v] > 0.5)) for v in range(n)}
    edges = []
    for i, j in np.argwhere(np.triu(A, 1) > 0.5):
        i, j = int(i), int(j)
        t = float(A2[i, j]); g2 = (f[i] - f[j]) ** 2
        symd = len(nbr[i] ^ nbr[j])
        den = (min(d[i], d[j]) - l2 + 1) ** 2
        eb = symd / den if den > 1e-12 else float("inf")     # gradient bound on g2
        edges.append((t, g2, t * g2, eb, t * eb, min(d[i], d[j]), max(d[i], d[j]), symd))
    edges = np.array(edges)  # cols: t, g2, prod, eb, t*eb, dmin, dmax, symd
    T = float(edges[:, 2].sum())
    T_bound = float(edges[:, 4].sum())
    valid = int(np.sum(edges[:, 1] <= edges[:, 3] + 1e-9))   # g2 <= bound?
    return dict(name=name, n=n, l2=l2, T=T, RHS=RHS, Required=Required, m=m,
                T_bound=T_bound, edges=edges, valid=valid, nedge=len(edges),
                Bok=(T <= RHS + 1e-7))


# ---- families ----
def lollipop(m, L): return nx.lollipop_graph(m, L)
def barbell(m, L): return nx.barbell_graph(m, L)
def chain(m, k):                          # k cliques K_m linked by single edges
    G = nx.complete_graph(m)
    for c in range(1, k):
        H = nx.relabel_nodes(nx.complete_graph(m), {i: i + c * m for i in range(m)})
        G = nx.union(G, H); G.add_edge((c - 1) * m, c * m)
    return G
def appendices(m, k, plen):
    G = nx.complete_graph(m); nxt = m
    for i in range(k):
        prev = i % m
        for _ in range(plen):
            G.add_edge(prev, nxt); prev = nxt; nxt += 1
    return G
def core_tendrils(m, p, k, tlen, seed):   # dense core G(m,p) + k sparse tendrils
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(m, p, seed=int(rng.integers(0, 2**31))); nxt = m
    for i in range(k):
        prev = int(rng.integers(0, m))
        for _ in range(tlen):
            G.add_edge(prev, nxt); prev = nxt; nxt += 1
    return G


def quadrants(edges):
    t = edges[:, 0]; g = edges[:, 1]; prod = edges[:, 2]
    tmed = np.median(t[t > 0]) if (t > 0).any() else 0.0
    gmed = np.median(g[g > 1e-15]) if (g > 1e-15).any() else 0.0
    hi_t = t > tmed; hi_g = g > gmed
    Q = {"Q1 hi-t/lo-g": hi_t & ~hi_g, "Q2 lo-t/hi-g": ~hi_t & hi_g,
         "Q3 hi-t/hi-g": hi_t & hi_g, "Q4 lo-t/lo-g": ~hi_t & ~hi_g}
    return tmed, gmed, {k: (int(v.sum()), float(prod[v].sum()),
                            float(prod[v].max()) if v.any() else 0.0) for k, v in Q.items()}


def main():
    cand = []
    for m in (10, 20, 50):
        for L in (3, 5, 10):
            cand.append((f"lollipop m={m} L={L}", lollipop(m, L)))
        for L in (3, 5):
            cand.append((f"barbell m={m} L={L}", barbell(m, L)))
    for m, k in ((10, 3), (20, 3), (15, 4)):
        cand.append((f"chain {k}xK_{m}", chain(m, k)))
    for m, k, pl in ((20, 5, 3), (20, 10, 5), (30, 5, 5)):
        cand.append((f"K{m}+{k}app(len{pl})", appendices(m, k, pl)))
    for m, p, k, tl in ((30, 0.5, 5, 4), (40, 0.4, 8, 5), (50, 0.5, 10, 6)):
        cand.append((f"core{m}p{p}+{k}tendril{tl}", core_tendrils(m, p, k, tl, 7)))

    rows = [quant(G, nm) for nm, G in cand]
    rows = [r for r in rows if r]
    pos = [r for r in rows if r["Required"] > 1e-9]

    print(f"families tested: {len(rows)}; Required>0: {len(pos)}; B holds: "
          f"{sum(r['Bok'] for r in rows)}/{len(rows)}")
    print("\n===== Required>0 families: gradient-bound test =====")
    print(f"{'family':28s} {'n':>4} {'λ₂':>6} {'T':>7} {'RHS':>7} {'Required':>8} "
          f"{'T_bnd':>9} {'T_bnd/RHS':>9} {'valid':>10}")
    for r in pos:
        print(f"{r['name']:28s} {r['n']:4d} {r['l2']:6.3f} {r['T']:7.3f} {r['RHS']:7.3f} "
              f"{r['Required']:8.3f} {r['T_bound']:9.2f} {r['T_bound']/r['RHS']:9.2f} "
              f"{r['valid']}/{r['nedge']}")
    if pos:
        print(f"\n  gradient bound CLOSES B (T_bound≤RHS): "
              f"{sum(1 for r in pos if r['T_bound']<=r['RHS']+1e-7)}/{len(pos)}")

    print("\n===== TASK 1: edge quadrants (ACTUAL t·grad²) on Required>0 families =====")
    for r in pos:
        tmed, gmed, Q = quadrants(r["edges"])
        q3n, q3c, q3m = Q["Q3 hi-t/hi-g"]
        print(f"  {r['name']:28s}: T={r['T']:.3f}  Q3(hi-t/hi-g): count={q3n} "
              f"contrib={q3c:.4f} ({100*q3c/(r['T']+1e-12):.1f}% of T)  maxprod={q3m:.2e}")

    print("\n===== TASK 4: hardest Required>0 graph — where is T_bound? =====")
    if pos:
        hard = max(pos, key=lambda r: r["T_bound"] / r["RHS"])
        e = hard["edges"]
        teb = e[:, 4]  # t*eb contributions to T_bound
        order = np.argsort(-teb)[:5]
        print(f"  hardest: {hard['name']} (T_bound/RHS={hard['T_bound']/hard['RHS']:.1f})")
        print(f"  top T_bound edges (t, grad², bound, t·bound, dmin, dmax, symd):")
        for k in order:
            print(f"     t={e[k,0]:.0f} g²={e[k,1]:.2e} bound={e[k,3]:.2e} t·bnd={e[k,4]:.3f} "
                  f"dmin={e[k,5]:.0f} dmax={e[k,6]:.0f} symd={e[k,7]:.0f}")
        # how much of T_bound is on high-t (clique) edges where actual g² is tiny?
        hi_t = e[:, 0] > np.median(e[e[:, 0] > 0, 0]) if (e[:, 0] > 0).any() else np.zeros(len(e), bool)
        print(f"  T_bound on hi-t edges: {teb[hi_t].sum():.2f} ({100*teb[hi_t].sum()/hard['T_bound']:.0f}%)  "
              f"but ACTUAL T there: {e[hi_t,2].sum():.4f}  => bound loose on clique edges")


if __name__ == "__main__":
    main()
