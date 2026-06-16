"""
Conjecture B — structure of the small-A regime via the COMPLEMENT graph.

Any graph is G = K_n − H, H = complement(G) (the 'missing-edge' graph). Classical
complement relation:  λ₂(G) = n − ν_max(H),  Fiedler(G) = top Laplacian eigenvector
f of H (ν_max).  This yields EXACT formulas (all verified here):

  d_v = (n-1) - deg_H(v),   δ = (n-1) - Δ_H,    (Δ_H = max H-degree)
  A   = fᵀDf - λ₂ = -fᵀA_H f - 1            (A_H = adjacency of H)
  S   = Σ d_v f_v = -Σ deg_H(v) f_v
  W   = Σ_{ab ∉ H} (Δ_H - max(deg_H a, deg_H b)) (f_a - f_b)²
  R'' = λ₂(A + 1 - S²/m).

So the small-A lock is entirely a statement about the (small) complement H.
This script: (1) verifies the identities; (2) closed forms for canonical families;
(3) edit-distance |H| classification; (4) perturbation K_n − (edges removed).

Run:  python conjecture_B_small_A_structure.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def quantities(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min())
    S = float(d @ f); fDf = float((d * f * f).sum()); A = fDf - l2; S2m = S * S / m
    Rpp = l2 * (A + 1 - S2m)
    W = 0.0
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        w = min(d[i], d[j]) - delta
        if w > 0:
            W += w * (f[i] - f[j]) ** 2
    return dict(n=n, m=m, d=d, delta=delta, l2=l2, f=f, S=S, fDf=fDf, A=A,
                S2m=S2m, Rpp=Rpp, W=W, idx=idx, nodes=nodes,
                WR=(W / Rpp if Rpp > 1e-12 else np.nan))


def complement_formulas(G):
    """Compute the same quantities via the complement H and check they match."""
    n = G.number_of_nodes()
    H = nx.complement(G)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    LH = nx.laplacian_matrix(H, nodelist=nodes).toarray().astype(float)
    AH = np.diag(LH.diagonal()) - LH
    degH = LH.diagonal().copy()
    evH, VH = np.linalg.eigh(LH); nu_max = float(evH[-1]); fH = VH[:, -1]
    fH = fH / np.linalg.norm(fH)
    DeltaH = float(degH.max())
    l2_pred = n - nu_max
    A_pred = -float(fH @ AH @ fH) - 1.0
    S_pred = -float(degH @ fH)
    # W via complement: sum over NON-edges of H of (DeltaH - max(degH))*(f_a-f_b)^2
    W_pred = 0.0
    for a in range(n):
        for b in range(a + 1, n):
            if not H.has_edge(nodes[a], nodes[b]):           # ab is an edge of G
                w = DeltaH - max(degH[a], degH[b])
                if w > 0:
                    W_pred += w * (fH[a] - fH[b]) ** 2
    return dict(H=H, nu_max=nu_max, DeltaH=DeltaH, degH=degH, fH=fH,
                l2_pred=l2_pred, A_pred=A_pred, S_pred=S_pred, W_pred=W_pred,
                edit=H.number_of_edges())


def verify():
    print("=== (1) verify complement identities on small-A graphs ===")
    rng = np.random.default_rng(7); errs = {"l2": 0, "A": 0, "S": 0, "W": 0}
    cnt = 0
    for _ in range(3000):
        n = int(rng.integers(8, 16)); p = float(rng.uniform(0.45, 0.97))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T) or ce.lambda2(T) <= 1e-6:
            continue
        q = quantities(G)
        if not (0 < q["A"] < 1.5):
            continue
        c = complement_formulas(G)
        # |S| sign can flip with eigenvector sign; compare S^2
        errs["l2"] = max(errs["l2"], abs(q["l2"] - c["l2_pred"]))
        errs["A"] = max(errs["A"], abs(q["A"] - c["A_pred"]))
        errs["S"] = max(errs["S"], abs(q["S"]**2 - c["S_pred"]**2))
        errs["W"] = max(errs["W"], abs(q["W"] - c["W_pred"]))
        cnt += 1
        if cnt >= 400:
            break
    print(f"   checked {cnt} small-A graphs; max abs errors:")
    print(f"     λ₂ = n - ν_max(H)        : {errs['l2']:.2e}")
    print(f"     A  = -fᵀA_H f - 1        : {errs['A']:.2e}")
    print(f"     S² = (Σ deg_H f)²        : {errs['S']:.2e}")
    print(f"     W  = Σ_{{ab∉H}}(Δ_H-max)·Δf² : {errs['W']:.2e}")


def families():
    print("\n=== (2) canonical families: closed forms (numeric vs derived) ===")
    # K_n - single edge
    print("\n  K_n - e  (H = single edge):  A=0, W=0, R''=n-2, W/R''=0")
    for n in (8, 12, 20):
        G = nx.complete_graph(n); G.remove_edge(0, 1)
        q = quantities(G)
        print(f"    n={n}: λ₂={q['l2']:.3f}(pred {n-2}) A={q['A']:.4f} W={q['W']:.4f} "
              f"R''={q['Rpp']:.3f} W/R''={q['WR']:.4f}")
    # K_n - star_k  (remove k edges at vertex 0)
    print("\n  K_n - star_k :  A=(k-1)/(k+1), λ₂=δ=n-k-1, "
          "W≈(n-1-k)(k-1)/(k+1) (S²/m→0), W/R''→(k-1)/(2k)")
    for n, k in [(20, 3), (20, 6), (30, 10), (40, 15)]:
        G = nx.complete_graph(n)
        for j in range(1, k + 1):
            G.remove_edge(0, j)
        q = quantities(G)
        A_pred = (k - 1) / (k + 1)
        W_pred = (n - 1 - k) * (k - 1) / (k + 1)
        WR_pred = (k - 1) / (2 * k)
        print(f"    n={n},k={k}: A={q['A']:.4f}(pred {A_pred:.4f}) λ₂={q['l2']:.2f}(δ={int(q['delta'])}) "
              f"W={q['W']:.3f}(pred {W_pred:.3f}) W/R''={q['WR']:.4f}(pred→{WR_pred:.4f})")
    # K_n - perfect matching (cocktail party) -- regular, W=0
    print("\n  K_n - perfect matching (cocktail party, regular): W=0")
    for n in (8, 12):
        G = nx.complete_graph(n)
        for i in range(0, n, 2):
            G.remove_edge(i, i + 1)
        q = quantities(G)
        print(f"    n={n}: λ₂={q['l2']:.3f} A={q['A']:.4f} W={q['W']:.4f} W/R''={q['WR']:.4f}")
    # K_n - triangle (remove a 3-clique's edges)
    print("\n  K_n - triangle (H=triangle):")
    for n in (10, 16):
        G = nx.complete_graph(n); G.remove_edges_from([(0,1),(1,2),(0,2)])
        q = quantities(G)
        print(f"    n={n}: λ₂={q['l2']:.3f} A={q['A']:.4f} W={q['W']:.4f} W/R''={q['WR']:.4f}")


def edit_distance():
    print("\n=== (3) edit distance to K_n (=|H|) and missing-edge pattern ===")
    rng = np.random.default_rng(11); rows = []
    pats = {"star": 0, "matching": 0, "sparse": 0, "dense-H": 0, "other": 0}
    for _ in range(4000):
        n = int(rng.integers(8, 16)); p = float(rng.uniform(0.45, 0.97))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T) or ce.lambda2(T) <= 1e-6:
            continue
        q = quantities(G)
        if not (0 < q["A"] < 1.5):
            continue
        H = nx.complement(G); eH = H.number_of_edges()
        dH = sorted((deg for _, deg in H.degree()), reverse=True)
        # crude pattern classify
        maxd = dH[0] if dH else 0
        if eH <= 1:
            pat = "sparse"
        elif maxd == eH and eH >= 2:
            pat = "star"
        elif maxd <= 1:
            pat = "matching"
        elif eH > n:
            pat = "dense-H"
        else:
            pat = "other"
        pats[pat] += 1
        rows.append((eH / (n * (n - 1) / 2.0), q["WR"], pat))
        if len(rows) >= 600:
            break
    fracs = np.array([r[0] for r in rows]); wr = np.array([r[1] for r in rows])
    print(f"   {len(rows)} small-A graphs.")
    print(f"   |H|/C(n,2) (missing-edge fraction): min={fracs.min():.2f} "
          f"median={np.median(fracs):.2f} max={fracs.max():.2f}")
    print(f"   pattern counts: {pats}")
    print(f"   corr(|H| fraction, W/R'') = {np.corrcoef(fracs, wr)[0,1]:+.3f}")
    # tight (W/R''>0.7) graphs: what's their H?
    tight = [r for r in rows if r[1] > 0.7]
    if tight:
        from collections import Counter
        print(f"   tight (W/R''>0.7): {len(tight)} graphs; H-patterns {dict(Counter(r[2] for r in tight))}; "
              f"|H| frac median={np.median([r[0] for r in tight]):.2f}")


def perturbation():
    print("\n=== (4) perturbation: K_n minus edges removed one at a time ===")
    rng = np.random.default_rng(3)
    for n in (20, 30):
        G = nx.complete_graph(n)
        edges = list(G.edges()); rng.shuffle(edges)
        print(f"\n  n={n}: remove random edges, track until A>=3/2 or disconnect")
        print(f"    {'#rm':>4s}{'λ₂':>8s}{'fᵀDf':>8s}{'A':>7s}{'S²/m':>7s}{'W':>8s}{'R̈':>8s}{'W/R̈':>7s}")
        removed = 0
        for e in edges:
            G.remove_edge(*e); removed += 1
            if not nx.is_connected(G):
                G.add_edge(*e); removed -= 1; continue
            if removed % max(1, n // 4) != 0 and removed > 1:
                continue
            q = quantities(G)
            tag = ""
            if q["A"] >= 1.5:
                tag = "  <-- A>=3/2 (leaving small-A)"
            print(f"    {removed:>4d}{q['l2']:>8.3f}{q['fDf']:>8.3f}{q['A']:>7.3f}"
                  f"{q['S2m']:>7.3f}{q['W']:>8.3f}{q['Rpp']:>8.3f}{q['WR']:>7.3f}{tag}")
            if q["A"] >= 1.5 or removed > n * 3:
                break


def main():
    verify()
    families()
    edit_distance()
    perturbation()


if __name__ == "__main__":
    main()
