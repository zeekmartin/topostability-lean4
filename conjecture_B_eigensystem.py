"""
Eigensystem / over-concentration analysis. On deg2+dense, the dense Fiedler solves
(L_d + E - lambda2 I) f_dense = f_v0 * chi_ab exactly; the dense block's spectral gap
(lambda2(block) >> lambda2(G)) forces f_dense uniform, giving Sigma_dense d f^2 -> q >= 2q-1.
Lollipop: clique uniform but low-mass (Fiedler on path). Run: python conjecture_B_eigensystem.py
"""
import numpy as np
import networkx as nx


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    nb = rng.choice(range(1, n), size=2, replace=False)
    for b in nb:
        G.add_edge(0, int(b))
    return G, [int(x) for x in nb]


def main():
    print("TASK 1-3: deg2+dense -- f_dense forced uniform by the eigensystem?")
    print(f"{'n':>5} {'q':>4} {'l2':>6} {'l2blk':>8} {'fv0^2':>7} {'mean_d':>9} "
          f"{'-fv0/(n-1)':>10} {'std/|m|':>8} {'Sig_dff':>8} {'q*fv0^2':>8} {'2q-1':>5}")
    for n in (50, 100, 200, 500):
        for q in (0.5, 0.65, 0.8):
            G, nb = deg2dense(n, q, 300 + n + int(100 * q))
            nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
            L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float); d = L.diagonal()
            ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
            v0 = idx[0]; fv0 = f[v0]; dense = [i for i in range(n) if i != v0]
            fd = f[dense]; dd = d[dense]; meand = fd.mean(); pred = -fv0 / (n - 1)
            stdrel = fd.std() / abs(meand) if meand != 0 else 0.0
            Sig = float((dd * fd * fd).sum())
            l2blk = np.linalg.eigvalsh(nx.laplacian_matrix(
                G.subgraph([nodes[i] for i in dense])).toarray().astype(float))[1]
            print(f"{n:5d} {q:4.2f} {l2:6.3f} {l2blk:8.2f} {fv0*fv0:7.4f} {meand:9.5f} "
                  f"{pred:10.5f} {stdrel:8.3f} {Sig:8.4f} {q*fv0*fv0:8.4f} {2*q-1:5.2f}")
    print("\nTASK 3 explicit system match (f_dense = (L_d+E-l2 I)^{-1} (fv0 chi_ab)):")
    for n in (50, 100, 200):
        G, nb = deg2dense(n, 0.65, 300 + n)
        nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float); d = L.diagonal()
        A = np.diag(d) - L; ev, V = np.linalg.eigh(L); l2 = ev[1]
        f = V[:, 1] / np.linalg.norm(V[:, 1]); v0 = idx[0]; fv0 = f[v0]
        dense = [i for i in range(n) if i != v0]
        Ld_full = np.diag(d[dense]) - A[np.ix_(dense, dense)]
        rhs = np.zeros(len(dense))
        for w in nb:
            rhs[dense.index(idx[w])] = fv0
        fd_solve = np.linalg.solve(Ld_full - l2 * np.eye(len(dense)), rhs)
        err = np.linalg.norm(fd_solve - f[dense]) / np.linalg.norm(f[dense])
        print(f"  n={n}: rel err = {err:.2e}")
    print("\nTASK 4 lollipop (clique uniform? mass split?):")
    for m, Lp in ((30, 5), (50, 10)):
        G = nx.lollipop_graph(m, Lp); nodes = list(G.nodes())
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float); d = L.diagonal()
        ev, V = np.linalg.eigh(L); l2 = ev[1]; f = V[:, 1] / np.linalg.norm(V[:, 1])
        clq = [i for i in range(len(nodes)) if d[i] >= m - 2]
        pth = [i for i in range(len(nodes)) if d[i] < m - 2]
        fc = f[clq]
        l2c = np.linalg.eigvalsh(nx.laplacian_matrix(
            G.subgraph([nodes[i] for i in clq])).toarray().astype(float))[1]
        print(f"  m={m} L={Lp}: l2={l2:.4f} l2(clq)={l2c:.1f} clq std/|m|="
              f"{fc.std()/abs(fc.mean()) if fc.mean()!=0 else float('inf'):.3f} "
              f"clq mass={float((fc*fc).sum()):.3f} path mass={float((f[pth]*f[pth]).sum()):.3f}")


if __name__ == "__main__":
    main()
