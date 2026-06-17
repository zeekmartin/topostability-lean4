"""
Direct Dirichlet-energy route for Conjecture B (no B2' / no min-degree relaxation):
   T = fᵀL_t f = Σ_ab t_ab(f_a-f_b)²  ≤  RHS = λ₂(fᵀQf - S²/m).
Q=D+A, S=Σ d_v f_v, m=|E|, t_ab=(A²)_ab.  T≤RHS ⟹ B (projected lift).

TASK 0: verify apex identity T = Σ_c E_{G[N(c)]}(f).
TASK 1: ratio T/RHS at scale (corpus + deg2+dense to n=1000).
TASK 2: gradient bound (f_a-f_b)² ≤ |N(a)△N(b)|·Σ_{u∈△}f_u²/(min(d_a,d_b)-λ₂)².
TASK 3: product bound T_bound = Σ t_ab·grad_bound vs RHS.
TASK 4: simpler aggregates (a) T≤λ₂fᵀDf  (b) T≤λ₂fᵀQf  (c) T≤max(t)·λ₂.
Run:  python conjecture_B_dirichlet_energy_route.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def base(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    A2 = A @ A
    T = 0.0
    for i, j in np.argwhere(np.triu(A, 1) > 0.5):
        T += A2[i, j] * (f[i] - f[j]) ** 2
    fQf = 2 * fDf - l2
    RHS = l2 * (fQf - S * S / m)
    return dict(G=G, nodes=nodes, idx=idx, n=n, m=m, L=L, d=d, A=A, A2=A2,
                l2=l2, f=f, fDf=fDf, S=S, T=float(T), fQf=fQf, RHS=RHS)


def corpus(maxn=9):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        Tg = ce.triangle_graph(G)
        if Tg.number_of_nodes() < 2 or not nx.is_connected(Tg):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def task0():
    print("===== TASK 0: apex identity  T = Σ_c E_{G[N(c)]}(f)  (no factor-2) =====")
    err = 0.0
    for G in [nx.complete_graph(6), nx.petersen_graph(), deg2dense(40, 0.6, 1),
              nx.gnp_random_graph(12, 0.5, seed=3)]:
        if not nx.is_connected(G):
            continue
        b = base(G); f = b["f"]; idx = b["idx"]
        apex = 0.0
        for c in G.nodes():
            Nc = list(G.neighbors(c))
            for x in range(len(Nc)):
                for y in range(x + 1, len(Nc)):
                    if G.has_edge(Nc[x], Nc[y]):
                        apex += (f[idx[Nc[x]]] - f[idx[Nc[y]]]) ** 2
        err = max(err, abs(apex - b["T"]))
    print(f"  max |Σ_c E_{{N(c)}}(f) - T| = {err:.2e}  => identity holds (E = Σ_edges, NO ½)")


def task1():
    print("\n===== TASK 1: ratio T/RHS at scale =====")
    rows = [base(G) for G in corpus(9)]
    rows = [r for r in rows if r["l2"] > 1e-6 and r["RHS"] > 1e-9]
    rr = np.array([r["T"] / r["RHS"] for r in rows])
    print(f"  corpus n≤9: max T/RHS={rr.max():.4f}  median={np.median(rr):.4f}  "
          f"(<1 on {int(np.sum(rr<=1+1e-9))}/{len(rows)})")
    print("  deg2+dense:")
    for n in (50, 100, 200, 500, 1000):
        rs = []
        for s in range(5 if n <= 200 else 2):
            G = deg2dense(n, 0.65, seed=900 + n + s)
            if nx.is_connected(G):
                b = base(G)
                if b["RHS"] > 1e-9:
                    rs.append(b["T"] / b["RHS"])
        if rs:
            print(f"    n={n:5d}: max T/RHS={max(rs):.4f}  (margin {1-max(rs):.4f})")


def sym_diff_bound(b):
    """per-edge: (f_a-f_b)² and the TASK-2 bound; return arrays + T_bound."""
    G = b["G"]; idx = b["idx"]; d = b["d"]; f = b["f"]; l2 = b["l2"]; A2 = b["A2"]
    nbr = {v: set(G.neighbors(v)) for v in G.nodes()}
    viol = 0; ratios = []; T_bound = 0.0; nedge = 0
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        grad2 = (f[i] - f[j]) ** 2
        sym = nbr[u].symmetric_difference(nbr[v])     # includes u,v themselves
        size = len(sym)
        msum = sum(f[idx[w]] ** 2 for w in sym)
        den = (min(d[i], d[j]) - l2) ** 2
        bound = size * msum / den if den > 1e-12 else float("inf")
        nedge += 1
        if grad2 > bound + 1e-9:
            viol += 1
        if bound > 1e-15:
            ratios.append(grad2 / bound)
        T_bound += A2[i, j] * bound
    return viol, nedge, np.array(ratios), float(T_bound)


def task23():
    print("\n===== TASK 2: gradient bound (f_a-f_b)² ≤ |N△|·Σ_△f²/(min(d)-λ₂)² =====")
    print("===== TASK 3: product bound T_bound = Σ t_ab·grad_bound vs RHS =====")
    # corpus
    rows = [base(G) for G in corpus(9)]
    rows = [r for r in rows if r["l2"] > 1e-6 and r["RHS"] > 1e-9]
    tv = 0; te = 0; allr = []; tb_ratio = []
    for r in rows:
        v, e, rr, tb = sym_diff_bound(r)
        tv += v; te += e
        if len(rr):
            allr.append(rr.max())
        tb_ratio.append(tb / r["RHS"])
    allr = np.array(allr); tb_ratio = np.array(tb_ratio)
    print(f"  [corpus] TASK2 edge violations: {tv}/{te}; max per-edge grad²/bound={allr.max():.3f}")
    print(f"  [corpus] TASK3 T_bound/RHS: max={tb_ratio.max():.3f} median={np.median(tb_ratio):.3f} "
          f"(<1 on {int(np.sum(tb_ratio<=1+1e-9))}/{len(rows)})")
    # deg2+dense scale
    for n in (50, 100, 200, 500):
        worst_v = 0; worst_tb = 0; cnt = 0
        for s in range(3 if n <= 200 else 1):
            G = deg2dense(n, 0.65, seed=900 + n + s)
            if not nx.is_connected(G):
                continue
            b = base(G)
            if b["RHS"] <= 1e-9:
                continue
            v, e, rr, tb = sym_diff_bound(b)
            worst_v += v; cnt += e; worst_tb = max(worst_tb, tb / b["RHS"])
        print(f"  [deg2+dense n={n}] TASK2 violations={worst_v}/{cnt}; TASK3 max T_bound/RHS={worst_tb:.3f}")


def task4():
    print("\n===== TASK 4: simpler aggregate bounds =====")
    def run(rows, label):
        a_T = []; a_le = []; b_le = []; c_le = []; cond = []
        for r in rows:
            T, RHS, l2, fDf, fQf = r["T"], r["RHS"], r["l2"], r["fDf"], r["fQf"]
            maxt = r["A2"][r["A"] > 0.5].max() if (r["A"] > 0.5).any() else 0
            a_T.append(T <= l2 * fDf + 1e-9)            # (a) T ≤ λ₂ fᵀDf
            a_le.append(l2 * fDf <= RHS + 1e-9)         # and λ₂fᵀDf ≤ RHS?
            b_le.append(T <= l2 * fQf + 1e-9)           # (b) T ≤ λ₂ fᵀQf
            c_le.append(T <= maxt * l2 + 1e-9)          # (c) T ≤ max(t)·λ₂
            cond.append(l2 + r["S"] ** 2 / r["m"] <= fDf + 1e-9)  # λ₂+S²/m ≤ fDf ?
        N = len(rows)
        print(f"  [{label}] (a) T≤λ₂fᵀDf: {sum(a_T)}/{N} | and λ₂fᵀDf≤RHS: {sum(a_le)}/{N} "
              f"| [λ₂+S²/m≤fDf: {sum(cond)}/{N}]")
        print(f"           (b) T≤λ₂fᵀQf: {sum(b_le)}/{N} | (c) T≤max(t)·λ₂: {sum(c_le)}/{N}")
    rows = [base(G) for G in corpus(9)]
    rows = [r for r in rows if r["l2"] > 1e-6 and r["RHS"] > 1e-9]
    run(rows, "corpus n≤9")
    sc = []
    for n in (50, 100, 200, 500, 1000):
        for s in range(3 if n <= 200 else 1):
            G = deg2dense(n, 0.65, seed=900 + n + s)
            if nx.is_connected(G):
                b = base(G)
                if b["RHS"] > 1e-9:
                    sc.append(b)
    run(sc, "deg2+dense n=50..1000")


if __name__ == "__main__":
    task0()
    task1()
    task23()
    task4()
