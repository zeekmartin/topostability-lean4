"""
Conjecture B — the exact lift bound and the restricted Ritz spectrum.

Operator identities (Lean-verified): L_t = B L_{T(G)} Bᵀ,  D+A = BBᵀ  (B = unsigned
incidence, |V|x|E|).  For φ⊥d, h=Bᵀφ:  φᵀL_tφ = hᵀL_{T(G)}h,  φᵀ(D+A)φ = hᵀh.
So  μ(G) = min_{φ⊥d} φᵀL_tφ/φᵀ(D+A)φ = MIN Ritz value of L_{T(G)} on
U_d := range(Bᵀ|_{d⊥})  (an (n-1)-dim subspace of ℝ^E, all ⊥ 1_E).

  Cauchy interlacing:  λ₂(T) ≤ μ(G).
  B (for connected non-bipartite G) holds if  μ(G) ≤ λ₂(G).

This script computes the FULL Ritz spectrum of L_{T(G)} on U_d and tests:
  (a) μ = MIN Ritz ≤ λ₂(G)            <- the correct target (sufficient for B)
  (b) MAX Ritz ≤ λ₂(G)               <- the 'for all φ' / spectral-radius target
  (c) the projected-Fiedler lift  R_T(h') = fᵀL_t f/(fᵀ(D+A)f - S²/m) ≤ λ₂(G)
on diverse graphs INCLUDING the lock-breaking 'deg-2 vertex + dense bg' family.

Run:  python conjecture_B_exact_lift.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def ritz_analysis(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    n = len(nodes); m = G.number_of_edges()
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    # non-bipartite & T(G) connected required
    T = ce.triangle_graph(G)
    if T.number_of_nodes() < 2 or not nx.is_connected(T):
        return None
    l2T = ce.lambda2(T)
    if l2T <= 1e-6:
        return None
    LT = nx.laplacian_matrix(T).toarray().astype(float)
    # unsigned incidence B (n x m), columns = edges in T-node order (G.edges())
    edges = list(G.edges())
    B = np.zeros((n, m))
    for e, (u, v) in enumerate(edges):
        B[idx[u], e] = 1.0; B[idx[v], e] = 1.0
    # basis of d^perp (n x (n-1))
    dvec = d / np.linalg.norm(d)
    Q1, _ = np.linalg.qr(np.eye(n) - np.outer(dvec, dvec))   # columns span R^n; project
    # better: explicit orthonormal basis of d^perp
    M = np.eye(n) - np.outer(dvec, dvec)
    U, s, _ = np.linalg.svd(M)
    P = U[:, s > 1e-9]                                       # n x (n-1), columns ⊥ d
    BtP = B.T @ P                                            # m x (n-1) = lifts of d^perp
    Qb, _ = np.linalg.qr(BtP)                                # orthonormal basis of U_d
    k = BtP.shape[1]
    Qb = Qb[:, :k]
    comp = Qb.T @ LT @ Qb                                    # (n-1)x(n-1) compression
    ritz = np.linalg.eigvalsh(0.5 * (comp + comp.T))
    mu = float(ritz[0]); ritz_max = float(ritz[-1]); ritz2 = float(ritz[1]) if k > 1 else mu

    # projected-Fiedler lift R_T(h')
    S = float(d @ f); fDf = float((d * f * f).sum())
    # f^T L_t f via incidence:
    h = B.T @ f
    fLtf = float(h @ LT @ h)
    den = fDf - S * S / m                                    # = f^T(D+A)f - S^2/m
    RT = fLtf / den if den > 1e-12 else float("inf")
    return dict(n=n, m=m, l2=l2, l2T=l2T, mu=mu, ritz_max=ritz_max, ritz2=ritz2,
                RT=RT, A=fDf - l2)


def families():
    out = []
    rng = np.random.default_rng(11)
    # small dense gnp
    for _ in range(400):
        n = int(rng.integers(8, 15)); p = float(rng.uniform(0.5, 0.95))
        out.append(("gnp", nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))))
    # WS near-regular
    for _ in range(200):
        n = int(rng.integers(12, 30)); k = int(rng.integers(6, min(16, n - 1)))
        out.append(("WS", nx.watts_strogatz_graph(n, k + (k % 2), float(rng.uniform(0.1, 0.5)),
                                                   seed=int(rng.integers(0, 2**31)))))
    # the LOCK-BREAKING family: one degree-2 vertex + dense G(n-1,q)
    for _ in range(400):
        n = int(rng.integers(16, 30)); q = float(rng.uniform(0.55, 0.72))
        Gb = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
        Gb = nx.relabel_nodes(Gb, {i: i + 1 for i in range(n - 1)})
        Gb.add_node(0)
        for b in rng.choice(range(1, n), size=2, replace=False):
            Gb.add_edge(0, int(b))
        out.append(("deg2+dense", Gb))
    return out


def main():
    rows = []
    for tag, G in families():
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        r = ritz_analysis(G)
        if r is None or r["l2"] <= 1e-6:
            continue
        r["tag"] = tag
        rows.append(r)
    N = len(rows)
    print(f"analysed {N} graphs (non-bipartite, T(G) connected)")

    def frac(pred):
        return 100.0 * np.mean([pred(r) for r in rows])

    print("\n=== min vs max Ritz value of L_{T(G)} on U_d = range(Bᵀ|_{d⊥}) ===")
    print(f"(a) μ = MIN Ritz ≤ λ₂(G)   [correct target, ⇒ B]   : {frac(lambda r: r['mu'] <= r['l2'] + 1e-7):.1f}%")
    print(f"(b) MAX Ritz ≤ λ₂(G)       ['for all φ' / radius]   : {frac(lambda r: r['ritz_max'] <= r['l2'] + 1e-7):.1f}%")
    print(f"(c) proj-Fiedler R_T(h') ≤ λ₂(G)  [lift bound]      : {frac(lambda r: r['RT'] <= r['l2'] + 1e-7):.1f}%")
    print(f"    interlacing λ₂(T) ≤ μ                            : {frac(lambda r: r['l2T'] <= r['mu'] + 1e-7):.1f}%")

    # magnitudes
    rmaxr = np.array([r["ritz_max"] / r["l2"] for r in rows])
    mur = np.array([r["mu"] / r["l2"] for r in rows])
    mu_vs_l2T = np.array([(r["mu"] - r["l2T"]) / max(r["l2T"], 1e-9) for r in rows])
    print(f"\n   MAX Ritz / λ₂(G):  median={np.median(rmaxr):.2f}  max={rmaxr.max():.2f}  "
          f"(>>1 ⇒ 'spectral radius ≤ λ₂' is FALSE)")
    print(f"   μ / λ₂(G):         median={np.median(mur):.3f}  max={mur.max():.3f}")
    print(f"   (μ−λ₂(T))/λ₂(T):   median={np.median(mu_vs_l2T):.4f}  max={mu_vs_l2T.max():.4f}  "
          f"(≈0 ⇒ lift near-optimal: μ≈λ₂(T))")

    # by family
    print("\n   by family:  μ≤λ₂ | maxRitz≤λ₂ | R_T≤λ₂ | median μ/λ₂ | median maxRitz/λ₂")
    from collections import defaultdict
    byf = defaultdict(list)
    for r in rows:
        byf[r["tag"]].append(r)
    for tag, rs in byf.items():
        a = 100 * np.mean([x["mu"] <= x["l2"] + 1e-7 for x in rs])
        b = 100 * np.mean([x["ritz_max"] <= x["l2"] + 1e-7 for x in rs])
        c = 100 * np.mean([x["RT"] <= x["l2"] + 1e-7 for x in rs])
        print(f"     {tag:12s}: {a:5.0f}% | {b:5.0f}% | {c:5.0f}% | "
              f"{np.median([x['mu']/x['l2'] for x in rs]):.3f} | "
              f"{np.median([x['ritz_max']/x['l2'] for x in rs]):.2f}")
    main.rows = rows


if __name__ == "__main__":
    main()
