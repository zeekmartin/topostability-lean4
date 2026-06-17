"""
Direct dissection of Required = λ₂·R, R = λ₂ + S²/m - fᵀDf, on deg2+dense.
Term-by-term scaling + eigen-equation at the bottleneck v₀ + Deficit-Required = RHS-T.
Run:  python conjecture_B_required_dissection.py
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


def row(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L; m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f); R = l2 + S * S / m - fDf
    Req = l2 * R
    v0 = int(np.argmax(f * f)); nb = np.flatnonzero(A[v0] > 0.5)
    fv0 = float(f[v0]); ab = float(f[nb].sum()); eigchk = (d[v0] - l2) * fv0
    A2 = A @ A; W = A * A2; Lt = np.diag(W @ np.ones(n)) - W; T = float(f @ Lt @ f)
    Deficit = l2 * fDf - T; RHS = l2 * (2 * fDf - l2 - S * S / m)
    return dict(n=n, l2=l2, S=S, S2m=S * S / m, fDf=fDf, R=R, Req=Req, fv0=fv0,
                ab=ab, eigchk=eigchk, T=T, Deficit=Deficit, RHS=RHS, m=m)


def main():
    ns = (50, 100, 200, 500, 1000)
    print("TASK 1/2: dissection of R and the eigen-equation at v₀")
    print(f"{'n':>5} {'lam2':>7} {'S':>9} {'S2/m':>7} {'fDf':>7} {'R':>7} {'Req':>8} "
          f"{'fv0^2':>7} {'a+b':>8} {'(2-l)fv0':>9}")
    for n in ns:
        r = row(deg2dense(n, 0.65, 300 + n))
        print(f"{n:5d} {r['l2']:7.3f} {r['S']:9.2f} {r['S2m']:7.3f} {r['fDf']:7.3f} "
              f"{r['R']:7.3f} {r['Req']:8.3f} {r['fv0']**2:7.4f} {r['ab']:8.3f} {r['eigchk']:9.3f}")
    print("\nTASK 3: Deficit-Required = RHS-T ;  reduction fᵀDf+fv0² ≥ λ₂+S²/m")
    print(f"{'n':>5} {'Deficit':>8} {'Req':>8} {'Def-Req':>8} {'RHS-T':>8} "
          f"{'l2*fv0^2':>9} {'fDf+fv0^2':>10} {'l2+S2/m':>8} {'margin':>7}")
    for n in ns:
        r = row(deg2dense(n, 0.65, 300 + n))
        lhs = r['fDf'] + r['fv0'] ** 2; rhs = r['l2'] + r['S2m']
        print(f"{n:5d} {r['Deficit']:8.3f} {r['Req']:8.3f} {r['Deficit']-r['Req']:8.3f} "
              f"{r['RHS']-r['T']:8.3f} {r['l2']*r['fv0']**2:9.3f} {lhs:10.3f} {rhs:8.3f} "
              f"{lhs-rhs:7.3f}")


if __name__ == "__main__":
    main()
