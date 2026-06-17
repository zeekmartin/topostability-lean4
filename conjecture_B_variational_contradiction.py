"""
TRACK A: variational contradiction test. For g = f + eps*p (p perp {1,f}),
R(g) - lambda2 = eps^2 * p^T(L-lambda2)p + O(eps^4) >= 0 (minimality).
Test whether p^T(L-lambda2)p = c * slack, slack = Deficit - Required = RHS - T.
If constant c>0 across graphs, minimality proves B. Run: python conjecture_B_variational_contradiction.py
"""
import numpy as np
import networkx as nx


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def proj(p, ones, f, n):
    p = p - (p @ ones / n) * ones
    p = p - (p @ f) * f
    return p


def test(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1]); ones = np.ones(n)
    fDf = float((d * f * f).sum()); S = float(d @ f)
    A2 = A @ A; W = A * A2; Lt = np.diag(W @ np.ones(n)) - W; T = float(f @ Lt @ f)
    RHS = l2 * (2 * fDf - l2 - S * S / m); slack = RHS - T
    if l2 * (l2 + S * S / m - fDf) <= 1e-9:
        return None
    M = L - l2 * np.eye(n)
    v0 = int(np.argmax(f * f)); nb = np.flatnonzero(A[v0] > 0.5)
    pa = np.zeros(n); pa[v0] = -f[v0]; pa[nb] = f[v0] / len(nb)
    pb = f * (d / d.mean() - 1)
    pc = -f * l2 / d
    res = {}
    for key, p in [('a', pa), ('b', pb), ('c', pc)]:
        pp = proj(p, ones, f, n)
        if np.linalg.norm(pp) < 1e-12:
            res[key] = (0.0, float('nan')); continue
        Ep = float(pp @ M @ pp)
        res[key] = (Ep, Ep / slack if abs(slack) > 1e-12 else float('nan'))
    return dict(n=n, l2=l2, slack=slack, res=res)


def main():
    print("TRACK A: E_p = p^T(L-l2)p  vs  slack = Deficit-Required ; want E_p = c*slack (const)")
    print(f"{'graph':16s} {'n':>5} {'slack':>8} | a:E_p/slack | b:E_p/slack | c:E_p/slack")
    gs = [("deg2dense", deg2dense(100, 0.65, 300)), ("deg2dense", deg2dense(200, 0.65, 500)),
          ("deg2dense", deg2dense(500, 0.65, 800)), ("lollipop50_10", nx.lollipop_graph(50, 10)),
          ("lollipop95_10", nx.lollipop_graph(95, 10)), ("lollipop45_5", nx.lollipop_graph(45, 5))]
    for nm, G in gs:
        r = test(G)
        if not r:
            print(f"{nm:16s} Required<=0"); continue
        a, b, c = r['res']['a'], r['res']['b'], r['res']['c']
        print(f"{nm:16s} {r['n']:5d} {r['slack']:8.4f} | {a[1]:11.3f} | {b[1]:11.3f} | {c[1]:11.3f}")
    print("\nE_p >= 0 always (minimality); none of a,b,c gives a constant ratio -> slack is "
          "not a 2nd variation of these directions.")


if __name__ == "__main__":
    main()
