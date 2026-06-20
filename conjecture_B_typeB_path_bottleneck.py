"""
TYPE B path-bottleneck: generalize the lollipop proof T=O(lam2^2), RHS=Theta(lam2).

Decompose triangle energy T = sum_e t_e (f_a-f_b)^2  (t_e = #common neighbours of edge e):
  T_block    : both endpoints in the triangle-rich block B
  T_path     : both endpoints triangle-free (path/stub P)   -> expect 0
  T_junction : one endpoint in B, one in P
Block B := vertices that lie in >=1 triangle; P := the rest (triangle-free).
gamma = lam2(G[B]) (block gap); boundary = #edges between B and P.

Verify: T_path=0, T_block=O(lam2^2), T_junction=O(lam2^2), RHS=Theta(lam2), T/RHS<=C lam2.
Run: python conjecture_B_typeB_path_bottleneck.py
"""
import numpy as np
import networkx as nx


def metrics(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f)
    A2 = A @ A                                   # A2[i,j] = #common neighbours = t_e on edges
    # block = vertices in a triangle  (diag of A^3 > 0)
    A3diag = np.einsum('ij,ji->i', A2, A)        # walks i->.->.->i = 2*triangles(i)
    inB = A3diag > 0.5
    # triangle energy split
    Tb = Tp = Tj = T = 0.0
    for u, v in G.edges():
        a, b = idx[u], idx[v]
        te = A2[a, b]; g = (f[a] - f[b]) ** 2; e = te * g; T += e
        if inB[a] and inB[b]:
            Tb += e
        elif (not inB[a]) and (not inB[b]):
            Tp += e
        else:
            Tj += e
    # RHS = lam2 * (sum_e h^2 - S^2/m)
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    RHS = lam * (Gsum - S ** 2 / m)
    # block gap gamma
    Bnodes = [nodes[i] for i in range(n) if inB[i]]
    gamma = np.nan
    if 2 <= len(Bnodes) < n:
        HB = G.subgraph(Bnodes)
        if nx.is_connected(HB):
            evB = np.linalg.eigvalsh(nx.laplacian_matrix(HB, nodelist=list(HB.nodes()))
                                     .toarray().astype(float))
            gamma = float(evB[1])
    boundary = int(sum(1 for u, v in G.edges() if inB[idx[u]] != inB[idx[v]]))
    return dict(n=n, lam=lam, T=T, Tb=Tb, Tp=Tp, Tj=Tj, RHS=RHS, gamma=gamma,
                boundary=boundary, blocksize=int(inB.sum()), m=m)


def tadpole(k, l):
    G = nx.complete_graph(k)
    prev = 0
    for i in range(l):
        nv = k + i; G.add_node(nv); G.add_edge(prev, nv); prev = nv
    return G


def families():
    fam = []
    for k in [5, 10, 20]:
        for l in [4, 8, 16, 32, 64]:
            fam.append((f"lollipop(K{k},P{l})", nx.lollipop_graph(k, l)))
    for k in [6, 12]:
        for l in [4, 8, 16, 32]:
            fam.append((f"barbell(K{k},P{l})", nx.barbell_graph(k, l)))
    for k in [8, 16]:
        for l in [8, 16, 32]:
            fam.append((f"tadpole(K{k},P{l})", tadpole(k, l)))
    return fam


def main():
    data = [(name, metrics(G)) for name, G in families()]

    print("=" * 104)
    print("TYPE B decomposition: T = T_block + T_path + T_junction;  scalings vs lam2")
    print("=" * 104)
    print(f"  {'graph':22s} {'lam2':>9} {'T':>9} {'T_block':>9} {'T_path':>8} {'T_junc':>8} "
          f"{'RHS':>9} {'gamma':>7} {'bdry':>5} {'T/RHS':>7}")
    for name, q in data:
        print(f"  {name:22s} {q['lam']:9.5f} {q['T']:9.5f} {q['Tb']:9.5f} {q['Tp']:8.1e} "
              f"{q['Tj']:8.1e} {q['RHS']:9.5f} {q['gamma']:7.2f} {q['boundary']:5d} {q['T']/q['RHS']:7.4f}")

    print("\n" + "=" * 104)
    print("STEP CHECKS")
    print("=" * 104)
    tp = max(q['Tp'] for _, q in data)
    print(f"  (a) T_path = 0 (path triangle-free)        : max T_path = {tp:.2e}")
    tjmax = max(q['Tj'] for _, q in data)
    print(f"  (b) T_junction = 0 (junction triangle-free): max T_junction = {tjmax:.2e}")
    # T_block = O(lam2^2): is T_block/lam2^2 bounded?
    r_b2 = [q['Tb'] / q['lam'] ** 2 for _, q in data]
    print(f"  (c) T_block / lam2^2 : min={min(r_b2):.2f} median={np.median(r_b2):.2f} max={max(r_b2):.2f}"
          f"  (bounded => T_block=O(lam2^2))")
    # RHS = Theta(lam2): RHS/lam2 bounded above & below?
    r_rhs = [q['RHS'] / q['lam'] for _, q in data]
    print(f"  (d) RHS / lam2       : min={min(r_rhs):.3f} median={np.median(r_rhs):.3f} max={max(r_rhs):.3f}"
          f"  (bounded both sides => RHS=Theta(lam2))")
    # T/RHS <= C lam2 ?
    r_c = [q['T'] / q['RHS'] / q['lam'] for _, q in data]
    print(f"  (e) (T/RHS)/lam2     : min={min(r_c):.2f} median={np.median(r_c):.2f} max={max(r_c):.2f}"
          f"  (bounded => T/RHS <= C lam2 -> 0)")
    print(f"  (f) gamma >> lam2    : min gamma/lam2 = {min(q['gamma']/q['lam'] for _,q in data):.1f}")
    print(f"  (g) boundary size    : max = {max(q['boundary'] for _,q in data)} "
          f"(O(1): lollipop/tadpole=1, barbell=2)")
    print(f"  T/RHS overall max    : {max(q['T']/q['RHS'] for _,q in data):.4f} (<= 0.18 claim)")

    print("\n" + "=" * 104)
    print("scaling with path length l (fixed block) — confirm lam2->0, T~lam2^2, RHS~lam2")
    print("=" * 104)
    for k in [10]:
        sub = [(name, q) for name, q in data if name.startswith(f"lollipop(K{k}")]
        ls = [4, 8, 16, 32, 64]
        print(f"  lollipop K{k}: " + " ".join(f"l={l}" for l in ls))
        print(f"    lam2     = " + " ".join(f"{q['lam']:.4f}" for _, q in sub))
        print(f"    T_block  = " + " ".join(f"{q['Tb']:.5f}" for _, q in sub))
        print(f"    T/lam2^2 = " + " ".join(f"{q['Tb']/q['lam']**2:.2f}" for _, q in sub))
        print(f"    RHS/lam2 = " + " ".join(f"{q['RHS']/q['lam']:.3f}" for _, q in sub))


if __name__ == "__main__":
    main()
