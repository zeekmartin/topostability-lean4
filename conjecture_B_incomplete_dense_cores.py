"""
TYPE A: incomplete dense cores as quasi-complete graphs (K_N minus edges).

G = H + v0 (v0~{a,b}), H dense on N=n_H vertices. Compare H to K_N.
Missing-edge variables (combinatorial) vs spectral gap quantities.
Run: python conjecture_B_incomplete_dense_cores.py
"""
import numpy as np
import networkx as nx
from itertools import combinations


def analyze(H, a=0, b=1):
    H = nx.convert_node_labels_to_integers(H); N = H.number_of_nodes()
    if not nx.is_connected(H): return None
    G = nx.Graph(H); G.add_node(N); G.add_edge(N, a); G.add_edge(N, b)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[N]
    if f[v0] < 0: f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    A2 = A @ A
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    # C split
    Catt = Cdense = 0.0
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        if d[i] > d[j]: t = (d[i] - d[j]) * f[i] * (f[i] - f[j])
        elif d[j] > d[i]: t = (d[j] - d[i]) * f[j] * (f[j] - f[i])
        else: t = 0.0
        if i == v0 or j == v0: Catt += t
        else: Cdense += t
    Rpp = lam * (fDf - lam + 1 - S ** 2 / m)
    # core resolvent / eff_resist + shifted resistance R_lambda
    LH = nx.laplacian_matrix(H, nodelist=list(range(N))).toarray().astype(float)
    mu, phi = np.linalg.eigh(LH); gamma = float(mu[1])
    inv = 1.0 / (mu[1:] - lam)
    R = (phi[:, 1:] * inv) @ phi[:, 1:].T
    eff = float(R[a, a] + R[b, b] - 2 * R[a, b])
    e = np.zeros(N); e[a] = 1; e[b] = -1
    R_lambda = float(e @ R @ e)                       # = eff (e_a-e_b perp 1)
    # missing-edge combinatorial variables
    NA = set(H.neighbors(a)); NB = set(H.neighbors(b))
    missing_edges = N * (N - 1) // 2 - H.number_of_edges()
    missing_inc_a = (N - 1) - H.degree(a)
    missing_inc_b = (N - 1) - H.degree(b)
    common = len((NA & NB) - {a, b})
    missing_common_ab = (N - 2) - common
    symdiff_ab = len((NA ^ NB) - {a, b})
    return dict(N=N, n=N + 1, m=m, lam=lam, gamma=gamma, gap=gap, eff=eff, R_lambda=R_lambda,
                Rpp=Rpp, Catt=Catt, Cdense=Cdense, fa=float(f[idx[a]]), fb=float(f[idx[b]]),
                fv0=float(f[v0]), missing_edges=missing_edges, missing_inc_a=missing_inc_a,
                missing_inc_b=missing_inc_b, missing_common_ab=missing_common_ab,
                symdiff_ab=symdiff_ab, gap_over_eff=gap / eff,
                gap_complete=10 * (N + 1 - 3) / (N * (N - 1) // 2 + 2))


def typeA(r): return r is not None and r['lam'] < r['gamma'] and r['fv0'] ** 2 > 0.3


def main():
    rng = np.random.default_rng(0)
    # build quasi-complete cores: K_N minus k random edges, various N,k
    data = []
    for N in [20, 30, 40]:
        for kfrac in [0.0, 0.02, 0.05, 0.1, 0.15, 0.2, 0.3]:
            for seed in range(4):
                H = nx.complete_graph(N)
                edges = list(H.edges()); rng2 = np.random.default_rng(seed * 100 + N)
                k = int(kfrac * len(edges))
                drop = rng2.choice(len(edges), size=k, replace=False)
                for di in drop: H.remove_edge(*edges[di])
                if not nx.is_connected(H): continue
                r = analyze(H)
                if typeA(r): data.append(r)
    print(f"  collected {len(data)} quasi-complete TYPE A graphs")

    print("\n" + "=" * 92)
    print("TASK 1 — missing-edge variables vs spectral quantities (Pearson r)")
    print("=" * 92)
    keys_x = ['missing_edges', 'missing_inc_a', 'missing_inc_b', 'missing_common_ab', 'symdiff_ab']
    keys_y = ['gap', 'gap_over_eff', 'Rpp', 'Catt', 'Cdense']
    print(f"  {'':18s} " + " ".join(f"{y:>12s}" for y in keys_y))
    for xk in keys_x:
        x = np.array([d[xk] for d in data], float)
        row = []
        for yk in keys_y:
            y = np.array([d[yk] for d in data], float)
            r = np.corrcoef(x, y)[0, 1] if x.std() > 0 else float('nan')
            row.append(f"{r:+12.3f}")
        print(f"  {xk:18s} " + " ".join(row))

    print("\n" + "=" * 92)
    print("TASK 2 — quasi-clique deletion: does gap drop below complete-core value?")
    print("=" * 92)
    for N in [25, 35]:
        gc = analyze(nx.complete_graph(N))['gap']
        print(f"  N={N}: complete-core gap = {gc:.5f}")
        # delete attachment-incident vs bulk edges, a few each
        for kind, picker in [("attach a-bulk", lambda H: [(0, u) for u in range(5, 12)]),
                             ("bulk-bulk", lambda H: [(5 + i, 6 + i) for i in range(0, 14, 2)])]:
            H = nx.complete_graph(N); gaps = [gc]
            for e in picker(H):
                if H.has_edge(*e):
                    H.remove_edge(*e); r = analyze(H)
                    if r and typeA(r): gaps.append(r['gap'])
            below = sum(1 for g in gaps if g < gc - 1e-9)
            print(f"    delete {kind:14s}: gaps {[round(g,4) for g in gaps]}  "
                  f"({'DROPS below complete' if below else 'stays >= complete'})")

    print("\n" + "=" * 92)
    print("TASK 3 — local incompleteness lemma candidates")
    print("=" * 92)
    gap = np.array([d['gap'] for d in data]); goe = np.array([d['gap_over_eff'] for d in data])
    gc = np.array([d['gap_complete'] for d in data])
    mca = np.array([d['missing_common_ab'] for d in data], float)
    m = np.array([d['m'] for d in data], float); Nn = np.array([d['N'] for d in data], float)
    # candidate A: gap - gap_complete vs missing_common_ab/m
    dA = gap - gc
    print(f"  (gap - gap_complete) vs missing_common_ab/m : corr = "
          f"{np.corrcoef(dA, mca/m)[0,1]:+.3f}  "
          f"(sign of (gap-gap_complete): {int((dA>0).sum())} pos / {int((dA<0).sum())} neg)")
    print(f"  gap_over_eff vs missing_common_ab/N         : corr = "
          f"{np.corrcoef(goe, mca/Nn)[0,1]:+.3f}")
    print(f"  gap_over_eff range: [{goe.min():.3f}, {goe.max():.3f}]; "
          f"is gap_over_eff >= c0 with c0={goe.min():.3f}")

    print("\n" + "=" * 92)
    print("TASK 4 — shifted resistance R_lambda = (e_a-e_b)^T (L_H-lam)^-1 (e_a-e_b)")
    print("=" * 92)
    rl = np.array([d['R_lambda'] for d in data]); eff = np.array([d['eff'] for d in data])
    print(f"  R_lambda == eff_resist ? max diff = {np.max(np.abs(rl-eff)):.2e} "
          f"(e_a-e_b perp 1 => same)")
    gorl = gap / rl
    print(f"  gap / R_lambda range: [{gorl.min():.3f}, {gorl.max():.3f}]")
    for xk in ['missing_common_ab', 'missing_inc_a', 'symdiff_ab']:
        x = np.array([d[xk] for d in data], float)
        print(f"  corr(gap/R_lambda, {xk:18s}) = {np.corrcoef(gorl, x)[0,1]:+.3f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print("  Which missing-edge variable best predicts gap / C_attach? Does deletion drop gap below")
    print("  complete? Is there a clean local-incompleteness lower bound?")


if __name__ == "__main__":
    main()
