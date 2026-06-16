"""
Conjecture B — is the lock W controlled by degree ordering, not Fiedler values?

Per vertex (unit Fiedler f, δ=min degree, N_v+ = {b~v : d_b>d_v}):
  W_v = (d_v-δ)·D_v+ ,  D_v+ = Σ_{b∈N_v+}(f_v-f_b)²      (actual lock contribution)
  H_v = (d_v-δ)·|N_v+|                                    (purely combinatorial)
  W = Σ_v W_v  (= the lock LHS);   ΣH := Σ_v H_v.

Note (proved):  ΣH = Σ_{ab∈E}(min(d_a,d_b)-δ)   (combinatorial; no f).
Note (proved):  every edge gradient (f_a-f_b)² ≤ Σ_e(f_a-f_b)² = λ₂, so
                W ≤ λ₂·ΣH  TRIVIALLY.  The question is whether λ₂·ΣH ≤ R''.

Tests items 1-5 from the brief on tight(52)+broad+dense datasets.
Run:  python conjecture_B_degree_ordering.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def per_graph(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min())
    S = float(d @ f); fDf = float((d * f * f).sum())
    Rpp = l2 * (fDf - l2 + 1.0 - S * S / m)
    Wv = np.zeros(n); Hv = np.zeros(n)
    m_up = 0; Sg_up = 0.0
    for u in nodes:
        i = idx[u]; Dp = 0.0; cnt = 0
        for b in G[u]:
            j = idx[b]
            if d[j] > d[i]:
                g = (f[i] - f[j]) ** 2
                Dp += g; cnt += 1; m_up += 1; Sg_up += g
            elif d[j] == d[i]:
                Dp += 0.5 * (f[i] - f[j]) ** 2; cnt += 0  # ties: no strict uphill count
        Wv[i] = (d[i] - delta) * Dp
        Hv[i] = (d[i] - delta) * cnt
    W = float(Wv.sum()); SH = float(Hv.sum())
    # combinatorial closed form check: ΣH = Σ_{ab}(min(d_a,d_b)-δ) over edges with d_a!=d_b
    SH_edge = sum(min(d[idx[u]], d[idx[v]]) - delta for u, v in G.edges()
                  if d[idx[u]] != d[idx[v]])
    # combinatorial bound: ΣH <= 1/2 Σ d_v^2 - m δ   (min<=avg, handshake)
    SH_bound = 0.5 * float((d * d).sum()) - m * delta
    return dict(n=n, m=m, delta=delta, Delta=float(d.max()), l2=l2, fDf=fDf, S=S,
                Rpp=Rpp, W=W, SH=SH, SH_edge=SH_edge, SH_bound=SH_bound,
                Wv=Wv, Hv=Hv, d=d, m_up=m_up, Sg_up=Sg_up,
                sigma2=float(np.var(d)))


def datasets():
    import conjecture_B_proof_v4_explore as v4
    tight = [G for _, G in v4.tight_graphs()]
    broad = [G for _, G in v4.broad_graphs(1500)]
    rng = np.random.default_rng(99); dense = []
    seen = set()
    while len(dense) < 800:
        n = int(rng.integers(8, 14)); p = float(rng.uniform(0.45, 0.95))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G):
            continue
        key = (n, G.number_of_edges(), nx.weisfeiler_lehman_graph_hash(G, iterations=2))
        if key in seen:
            continue
        seen.add(key); dense.append(G)

    def keep(G):
        T = ce.triangle_graph(G)
        return T.number_of_nodes() >= 2 and nx.is_connected(T) and ce.lambda2(T) > TOL
    return ([G for G in tight if keep(G)],
            [G for G in broad if keep(G)],
            [G for G in dense if keep(G)])


def pear(x, y):
    x = np.asarray(x, float); y = np.asarray(y, float)
    if len(x) < 3 or np.std(x) < 1e-14 or np.std(y) < 1e-14:
        return np.nan
    return float(np.corrcoef(x, y)[0, 1])


def main():
    tight, broad, dense = datasets()
    allG = {"tight": tight, "broad": broad, "dense": dense}
    rows = {k: [per_graph(G) for G in gs] for k, gs in allG.items()}

    # verify closed form ΣH = Σ_edges(min-δ)
    err = max(abs(r["SH"] - r["SH_edge"]) for rs in rows.values() for r in rs)
    print(f"[check] ΣH = Σ_edges(min(d_a,d_b)-δ): max err {err:.2e}")
    bnd_ok = all(r["SH"] <= r["SH_bound"] + 1e-7 for rs in rows.values() for r in rs)
    print(f"[check] ΣH <= ½Σd_v² - mδ (combinatorial bound): {'holds' if bnd_ok else 'FAILS'}")

    # ---- 1. correlation W_v vs H_v ----
    print("\n[1] corr(W_v, H_v):")
    for k, rs in rows.items():
        pooled_W = np.concatenate([r["Wv"] for r in rs])
        pooled_H = np.concatenate([r["Hv"] for r in rs])
        pg = [pear(r["Wv"], r["Hv"]) for r in rs]
        pg = [x for x in pg if x == x]
        print(f"  {k:6s}: pooled r={pear(pooled_W, pooled_H):+.3f}  "
              f"per-graph mean r={np.mean(pg):+.3f}")

    # ---- 2. ratio W_v/H_v (avg uphill gradient): bounded by λ₂? ----
    print("\n[2] ratio W_v/H_v (= avg uphill gradient²), vs λ₂:")
    for k, rs in rows.items():
        ratios = []; vs_l2 = []
        for r in rs:
            if r["l2"] < 1e-9:
                continue
            mask = r["Hv"] > 0
            rr = r["Wv"][mask] / r["Hv"][mask]
            ratios.extend(rr.tolist())
            vs_l2.extend((rr / r["l2"]).tolist())
        ratios = np.array(ratios); vs_l2 = np.array(vs_l2)
        print(f"  {k:6s}: max(W_v/H_v)={ratios.max():.4f}  "
              f"max((W_v/H_v)/λ₂)={vs_l2.max():.4f} (<=1 ⇒ bounded by λ₂)")

    # ---- 3. global W/ΣH per graph: bounded by λ₂? how loose? ----
    print("\n[3] global ρ = W/ΣH per graph, vs λ₂:")
    for k, rs in rows.items():
        rl = np.array([r["W"] / r["SH"] / r["l2"] for r in rs
                       if r["SH"] > 1e-12 and r["l2"] > 1e-9])
        print(f"  {k:6s}: max ρ/λ₂={np.max(rl):.4f} (<=1 ⇒ ρ≤λ₂)  "
              f"median ρ/λ₂={np.median(rl):.4f} (looseness)")

    # ---- 4. ΣH combinatorial magnitude vs fDf ----
    print("\n[4] ΣH (combinatorial) vs fᵀDf:")
    for k, rs in rows.items():
        sh = np.array([r["SH"] for r in rs]); fdf = np.array([r["fDf"] for r in rs])
        print(f"  {k:6s}: median ΣH={np.median(sh):.2f}  median fᵀDf={np.median(fdf):.2f}  "
              f"median ΣH/fᵀDf={np.median(sh/np.maximum(fdf,1e-9)):.2f}")

    # ---- 5. the proposed reductions ----
    print("\n[5] reduction tests (trivial gradient bound):")
    for k, rs in rows.items():
        n = len(rs)
        W_le = sum(1 for r in rs if r["W"] <= r["l2"] * r["SH"] + 1e-7)      # W<=λ₂ΣH (trivial)
        l2SH_le = sum(1 for r in rs if r["l2"] * r["SH"] <= r["Rpp"] + 1e-7)  # λ₂ΣH<=R''
        Wlock = sum(1 for r in rs if r["W"] <= r["Rpp"] + 1e-7)             # the lock itself
        print(f"  {k:6s}: W<=λ₂·ΣH {W_le}/{n} | λ₂·ΣH<=R'' {l2SH_le}/{n} | lock W<=R'' {Wlock}/{n}")

    # ---- 6. Chebyshev sum inequality (anticorrelation -> oppositely sorted) ----
    # If weight w_e=(min-δ) and gradient g_e are oppositely ordered over uphill edges,
    #   W = Σ w_e g_e  ≤  (1/m_up)(Σ w_e)(Σ g_e) = ΣH · Sg_up / m_up   (Chebyshev).
    # Sg_up = Σ_uphill g_e ≤ λ₂.  Test the bound and whether it closes ≤ R''.
    print("\n[6] Chebyshev-sum bound  CB = ΣH·Sg_up/m_up  (and CB' = ΣH·λ₂/m_up):")
    for k, rs in rows.items():
        n = len(rs); Wle_CB = 0; CB_le = 0; Wle_CBp = 0; CBp_le = 0
        for r in rs:
            if r["m_up"] == 0:
                Wle_CB += 1; CB_le += 1; Wle_CBp += 1; CBp_le += 1; continue
            CB = r["SH"] * r["Sg_up"] / r["m_up"]
            CBp = r["SH"] * r["l2"] / r["m_up"]
            if r["W"] <= CB + 1e-9: Wle_CB += 1
            if CB <= r["Rpp"] + 1e-7: CB_le += 1
            if r["W"] <= CBp + 1e-9: Wle_CBp += 1
            if CBp <= r["Rpp"] + 1e-7: CBp_le += 1
        print(f"  {k:6s}: W<=CB {Wle_CB}/{n} | CB<=R'' {CB_le}/{n} || "
              f"W<=CB' {Wle_CBp}/{n} | CB'<=R'' {CBp_le}/{n}")

    main.rows = rows


if __name__ == "__main__":
    main()
