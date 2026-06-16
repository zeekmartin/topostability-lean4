"""
Multi-spectral attack on  target := C+R'' ≥ 0  (B2' slack).
C = Σ(d_h-d_l)f_h(f_h-f_l), R'' = λ₂(fᵀDf-λ₂+1-S²/m).  f=u_2 (unit Fiedler).

TASK 1: decompose d = Σ β_i u_i (β_i=dᵀu_i); is target = Σ_{i≥3} g(β_i,λ_i,λ₂)?
        test resolvent form  Σ_{i≥3} β_i²/(λ_i-λ₂).
TASK 2: M = λ₂Q - L_t (Q=D+A, L_t triangle-weighted Lap); negative eigvecs v_j (μ_j<0):
        does the Fiedler avoid the most-negative cone? |fᵀv_j|² vs μ_j.
TASK 3: Taylor around K_n: target for K_n-e, -triangle, -matching(k), -star(k).
TASK 4: correlations of target with gap, β_3², resolvent, degree-variance-on-f.
Run:  python conjecture_B_multispectral.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def tri_laplacian(G, nodes, idx):
    n = len(nodes); Lt = np.zeros((n, n))
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        t = len(set(G[u]) & set(G[v]))
        Lt[i, j] -= t; Lt[j, i] -= t; Lt[i, i] += t; Lt[j, j] += t
    return Lt


def data(G, want_M=False):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    S = float(d @ f); fDf = float((d * f * f).sum()); fD2f = float((d * d * f * f).sum())
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    C = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        h, lo = (i, j) if d[i] >= d[j] else (j, i)
        C += (d[h] - d[lo]) * f[h] * (f[h] - f[lo])
    target = C + Rpp
    beta = V.T @ d                       # β_i = dᵀu_i  (length n, index 0..n-1)
    gap = float(ev[2] - l2) if n > 2 else 0.0
    beta3sq = float(beta[2] ** 2) if n > 2 else 0.0
    resolv = float(sum(beta[i] ** 2 / (ev[i] - l2) for i in range(2, n) if ev[i] - l2 > 1e-9))
    degvar = fD2f - fDf ** 2
    out = dict(n=n, m=m, l2=l2, S=S, fDf=fDf, Rpp=Rpp, C=C, target=target,
               gap=gap, beta3sq=beta3sq, resolv=resolv, degvar=degvar)
    if want_M:
        Q = np.diag(d) + A; Lt = tri_laplacian(G, nodes, idx)
        M = l2 * Q - Lt
        ones = np.ones(n); P = np.eye(n) - np.outer(ones, ones) / n
        Mp = P @ M @ P
        w, U = np.linalg.eigh(Mp)
        drop = int(np.argmax(np.abs(U.T @ ones)))   # the ~1 direction
        recs = []
        for j in range(n):
            if j == drop:
                continue
            recs.append((float(w[j]), float(U[:, j] @ f), float(U[:, j] @ d)))
        out["Mspec"] = recs
        out["fMf"] = float(f @ M @ f)
    return out


def corpus(maxn=9):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def corr(x, y):
    x = np.asarray(x); y = np.asarray(y)
    return float(np.corrcoef(x, y)[0, 1])


def main():
    graphs = corpus(9)
    rows = [data(G) for G in graphs]
    rows = [r for r in rows if r["l2"] > 1e-6]
    N = len(rows)
    tgt = np.array([r["target"] for r in rows])
    print(f"distinct corpus graphs: {N};  target=C+R'' min={tgt.min():.5f}")

    # ===== TASK 1: resolvent / mode-sum =====
    print("\n===== TASK 1: spectral decomposition of target =====")
    resolv = np.array([r["resolv"] for r in rows])
    c = float(resolv @ tgt / (resolv @ resolv))
    pred = c * resolv
    ss = 1 - ((tgt - pred) ** 2).sum() / ((tgt - tgt.mean()) ** 2).sum()
    print(f"  resolvent Σ_{{i≥3}}β_i²/(λ_i-λ₂): corr={corr(resolv,tgt):+.3f} "
          f"best-c={c:.3f} R²={ss:+.3f}")
    print(f"  (β_i=dᵀu_i; S=β_2 enters R'' as -λ₂β_2²/m)")
    # is target a clean nonneg mode-sum? -> reported via the above fit quality

    # ===== TASK 2: negative-cone avoidance =====
    print("\n===== TASK 2: Fiedler vs negative cone of M=λ₂Q-L_t =====")
    mrows = [data(G, want_M=True) for G in graphs[:1500] if nx.is_connected(G)]
    mrows = [r for r in mrows if r["l2"] > 1e-6]
    # collect (μ_j, |fᵀv_j|², |dᵀv_j|²) for negative μ
    neg_mu = []; neg_fov = []; allpairs = []
    nB = 0
    for r in mrows:
        if r["fMf"] >= -1e-6:
            nB += 1
        for mu, fv, dv in r["Mspec"]:
            allpairs.append((mu, fv * fv))
            if mu < -1e-6:
                neg_mu.append(mu); neg_fov.append(fv * fv)
    print(f"  fᵀMf≥0 (B holds): {nB}/{len(mrows)}")
    neg_mu = np.array(neg_mu); neg_fov = np.array(neg_fov)
    # correlation between how-negative and overlap: if Fiedler avoids, corr(|μ|,|fv|²)<0
    print(f"  negative directions: {len(neg_mu)} total; "
          f"corr(μ_j, |fᵀv_j|²)={corr(neg_mu,neg_fov):+.3f} "
          f"(μ more negative ⇒ overlap {'SMALLER (avoidance!)' if corr(neg_mu,neg_fov)>0 else 'larger'})")
    # bin by μ
    print("  |fᵀv_j|² averaged by μ_j bin (negative side):")
    for lo, hi in [(-1e9, -10), (-10, -3), (-3, -1), (-1, -0.1), (-0.1, 0)]:
        mask = (neg_mu >= lo) & (neg_mu < hi)
        if mask.sum():
            print(f"    μ∈[{lo if lo>-1e8 else '-inf':>4},{hi:>5}): "
                  f"mean|fᵀv|²={neg_fov[mask].mean():.4f}  n={int(mask.sum())}")
    # compare overlap on most-negative vs most-positive
    allp = np.array(allpairs)
    most_neg = allp[allp[:, 0] < np.percentile(allp[:, 0], 10)]
    most_pos = allp[allp[:, 0] > np.percentile(allp[:, 0], 90)]
    print(f"  mean|fᵀv|² on most-NEG decile μ: {most_neg[:,1].mean():.4f}  "
          f"vs most-POS decile: {most_pos[:,1].mean():.4f}")

    # ===== TASK 3: Taylor around K_n =====
    print("\n===== TASK 3: perturbation K_n - H =====")
    def km(n, removed):
        G = nx.complete_graph(n); G.remove_edges_from(removed); return G
    for n in (8, 10, 14):
        base = nx.complete_graph(n)
        e1 = km(n, [(0, 1)])
        tri = km(n, [(0, 1), (0, 2), (1, 2)])
        match = km(n, [(0, 1), (2, 3), (4, 5)])             # 3 disjoint edges
        star = km(n, [(0, 1), (0, 2), (0, 3)])              # 3 edges at vertex 0
        for nm, G in [("K_n-e", e1), ("K_n-△", tri), ("K_n-match3", match), ("K_n-star3", star)]:
            if nx.is_connected(G) and nx.is_connected(ce.triangle_graph(G)):
                r = data(G)
                print(f"  n={n:2d} {nm:11s}: C+R''={r['target']:.4f}  (C={r['C']:.4f} R''={r['Rpp']:.4f})")
    # leading order in k: matching (k disjoint edges) vs star (k edges at a vertex)
    print("  scaling vs k (n=16):")
    n = 16
    for k in (1, 2, 3, 4, 5):
        Gm = km(n, [(2 * i, 2 * i + 1) for i in range(k)])
        Gs = km(n, [(0, i + 1) for i in range(k)])
        rm = data(Gm) if nx.is_connected(ce.triangle_graph(Gm)) else None
        rs = data(Gs) if nx.is_connected(ce.triangle_graph(Gs)) else None
        sm = f"{rm['target']:.3f}" if rm else "n/a"
        ssg = f"{rs['target']:.3f}" if rs else "n/a"
        print(f"    k={k}: matching C+R''={sm:>8}   star C+R''={ssg:>8}")

    # ===== TASK 4: correlation diagnostic =====
    print("\n===== TASK 4: which predicts C+R'' best? =====")
    for name in ["gap", "beta3sq", "resolv", "degvar"]:
        x = np.array([r[name] for r in rows])
        cc = corr(x, tgt)
        cfit = float(x @ tgt / (x @ x)) if x @ x > 0 else 0.0
        r2 = 1 - ((tgt - cfit * x) ** 2).sum() / ((tgt - tgt.mean()) ** 2).sum()
        label = {"gap": "λ_3-λ_2", "beta3sq": "β_3²",
                 "resolv": "Σβ_i²/(λ_i-λ₂)", "degvar": "fᵀD²f-(fᵀDf)²"}[name]
        print(f"  {label:18s}: corr={cc:+.3f}  best-c R²={r2:+.3f}")
    main.rows = rows


if __name__ == "__main__":
    main()
