"""
B2' ⟺ C ≥ -R'',  C = Σ_{ab}(d_h-d_l) f_h(f_h-f_l),  R'' = λ₂(fᵀDf-λ₂+1-S²/m).
target := C + R''  (= RHS - W1 ≥ 0, the B2' slack).

TASK 1: R'' ≥ 0  ⟺  m(fᵀAf+1) ≥ S²  ⟺  fᵀ N f ≥ 0, N := mA + mI - ddᵀ.
        Decisive test: is N ⪰ 0 on 1⊥ ? (if yes → pure linear algebra, no eigen-eq).
TASK 2: second-variation candidates g_i ⊥ {1,f}; E_i = g_iᵀ(L-λ₂)g_i ≥ 0.
TASK 3: is target = g_iᵀ(L-λ₂)g_i exactly (rescaled)? best lin-combo over {E_i, cross}.
Run:  python conjecture_B2prime_variational.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def proj(w, ones, f, n):
    """project vector w onto {1,f}^perp  (f unit, ones = all-ones, ||1||²=n)."""
    w = w - (w @ ones / n) * ones
    w = w - (w @ f) * f
    return w


def data(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    ones = np.ones(n)
    S = float(d @ f); fDf = float((d * f * f).sum())
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    # C (oriented)
    C = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        h, lo = (i, j) if d[i] >= d[j] else (j, i)
        C += (d[h] - d[lo]) * f[h] * (f[h] - f[lo])
    target = C + Rpp
    # --- TASK 1: matrix N = mA + mI - ddᵀ ---
    N = m * A + m * np.eye(n) - np.outer(d, d)
    # smallest eigenvalue of N restricted to 1⊥ : project N onto 1⊥ basis
    # build orthonormal basis of 1⊥
    Q, _ = np.linalg.qr(np.eye(n) - np.outer(ones, ones) / n)  # not clean; use Householder
    # simpler: eigh of P N P with P=I-11ᵀ/n, ignore the ~0 eigenvector along 1
    P = np.eye(n) - np.outer(ones, ones) / n
    Nperp = P @ N @ P                       # 1 ∈ ker(P) so 1 is an eigenvector w/ eigenvalue 0
    wN, UN = np.linalg.eigh(Nperp)
    drop = int(np.argmax(np.abs(UN.T @ ones)))   # the eigenvector most aligned with 1
    minN = float(min(wN[k] for k in range(n) if k != drop))
    # --- TASK 2: candidate perturbations ---
    Df = d * f
    g1 = proj(Df, ones, f, n)
    g2 = proj(d.copy(), ones, f, n)
    g3 = proj((d - d.mean()) * f, ones, f, n)
    g4 = proj(np.array([sum((d[idx[u]] - d[idx[w]]) * f[idx[w]] for w in G[u]) for u in nodes]),
              ones, f, n)            # g4 = [D,A]f projected
    gs = [g1, g2, g3, g4]
    Lm = L - l2 * np.eye(n)
    E = [float(g @ Lm @ g) for g in gs]
    # cross energies for lin-combo span
    cross = {}
    for a in range(4):
        for b in range(a, 4):
            cross[(a, b)] = float(gs[a] @ Lm @ gs[b])
    # uᵢᵀN uᵢ for every L-eigenvector u_i (i≥2): m(uᵢᵀD uᵢ - λᵢ + 1) - (dᵀuᵢ)²
    uNu = []
    for i in range(1, n):
        ui = V[:, i] / np.linalg.norm(V[:, i]); li = float(ev[i])
        uNu.append(m * (float((d * ui * ui).sum()) - li + 1) - float(d @ ui) ** 2)
    return dict(n=n, m=m, l2=l2, S=S, fDf=fDf, Rpp=Rpp, C=C, target=target,
                minN=minN, E=E, cross=cross, uNu=uNu,
                fAf=fDf - l2, lhsT1=m * (fDf - l2 + 1), rhsT1=S * S)


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


def main():
    graphs = corpus(9)
    rows = [data(G) for G in graphs]
    rows = [r for r in rows if r["l2"] > 1e-6]
    N = len(rows)
    print(f"distinct corpus graphs: {N}")

    # ===== TASK 1 =====
    print("\n===== TASK 1: R'' ≥ 0  ⟺  m(fᵀAf+1) ≥ S² =====")
    rpp = np.array([r["Rpp"] for r in rows])
    print(f"  R'' : min={rpp.min():.6f}  (≥0 on {int(np.sum(rpp>=-1e-9))}/{N})")
    gapT1 = np.array([r["lhsT1"] - r["rhsT1"] for r in rows])
    print(f"  m(fᵀAf+1) - S² : min={gapT1.min():.6f}  (≥0 on {int(np.sum(gapT1>=-1e-6))}/{N})")
    minN = np.array([r["minN"] for r in rows])
    print(f"  λ_min(N|_1⊥), N=mA+mI-ddᵀ : min={minN.min():.4f}  median={np.median(minN):.4f}")
    npos = int(np.sum(minN >= -1e-6))
    print(f"    N ⪰ 0 on 1⊥ : {npos}/{N} graphs  "
          f"=> {'PURE LINEAR ALGEBRA (no eigen-eq needed!)' if npos==N else 'NOT PSD -> R''≥0 NEEDS the Fiedler/eigen-equation'}")
    # does eigen-eq ALONE suffice, or is λ₂-MINIMALITY needed?  test uᵢᵀNuᵢ for every L-eigenvector
    badhi = 0; tot = 0
    for r in rows:
        for v in r.get("uNu", []):
            tot += 1
            if v < -1e-6:
                badhi += 1
    if tot:
        print(f"    uᵢᵀN uᵢ ≥ 0 over ALL L-eigenvectors (i≥2): fails {badhi}/{tot} "
              f"=> {'eigen-eq alone INSUFFICIENT, need λ₂ MINIMALITY' if badhi else 'holds for every eigenvector (eigen-eq structure enough)'}")

    # ===== TASK 2 / 3 =====
    print("\n===== TASK 2/3: second-variation candidates =====")
    tgt = np.array([r["target"] for r in rows])
    print(f"  target = C+R'' : min={tgt.min():.6f} (≥0 ⟺ B2')  median={np.median(tgt):.4f}")
    names = ["g1=Df", "g2=deg", "g3=(d-d̄)f", "g4=[D,A]f"]
    Emat = np.array([r["E"] for r in rows])  # N x 4
    for i, nm in enumerate(names):
        Ei = Emat[:, i]
        nn = int(np.sum(Ei >= -1e-7))
        # correlation & best single-scalar fit target ≈ c*Ei
        c = float(Ei @ tgt / (Ei @ Ei)) if Ei @ Ei > 0 else 0.0
        resid = tgt - c * Ei
        ss = 1 - (resid @ resid) / ((tgt - tgt.mean()) @ (tgt - tgt.mean()))
        corr = float(np.corrcoef(Ei, tgt)[0, 1])
        # affine fit target ≈ a + b·E
        M = np.vstack([np.ones(N), Ei]).T
        (a, b), *_ = np.linalg.lstsq(M, tgt, rcond=None)
        rss = tgt - (a + b * Ei)
        ssa = 1 - (rss @ rss) / ((tgt - tgt.mean()) @ (tgt - tgt.mean()))
        print(f"  {nm:11s}: E≥0 {nn}/{N}  corr={corr:+.3f}  R²(c·E)={ss:+.2f}  "
              f"affine R²={ssa:+.3f} (a={a:.2f},b={b:.3f})  maxResid={np.abs(resid).max():.2f}")

    # full span: target ~ linear combo of {E_i} and cross-energies X_ij  (basis of any cᵀMc)
    feats = []; labels = []
    for i in range(4):
        feats.append(Emat[:, i]); labels.append(f"E{i+1}")
    for a in range(4):
        for b in range(a + 1, 4):
            feats.append(np.array([r["cross"][(a, b)] for r in rows])); labels.append(f"X{a+1}{b+1}")
    Xf = np.array(feats).T  # N x 10
    coef, *_ = np.linalg.lstsq(Xf, tgt, rcond=None)
    pred = Xf @ coef
    resid = tgt - pred
    ss = 1 - (resid @ resid) / ((tgt - tgt.mean()) @ (tgt - tgt.mean()))
    print(f"\n  lin-combo of {{E_i, X_ij}} (span of all second-variation quadratics in g1..g4):")
    print(f"    R²={ss:.5f}  maxResid={np.abs(resid).max():.4f}  mean|resid|={np.abs(resid).mean():.4f}")
    print("    coefs:", {labels[k]: round(float(coef[k]), 3) for k in range(len(labels))})

    main.rows = rows


if __name__ == "__main__":
    main()
