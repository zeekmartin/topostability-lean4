"""
Conjecture B — decompose the exact lock on the HARD REGIME only.

Hard regime: large, near-regular, low-μ₂, high-ΣH (Watts-Strogatz-type) graphs
where W ≤ μ₂·fᵀDf and other proxy bounds fail (α = W/(μ₂fᵀDf) > 1).

Lock:  W ≤ R'' = λ₂·fᵀDf - λ₂² + λ₂ - λ₂·S²/m   (S = Σ d_v f_v).
Terms: T1 = λ₂·fᵀDf,  T2 = -λ₂²,  T3 = +λ₂ (the "+1"),  T4 = -λ₂·S²/m.

For each hard graph tabulate W, T1..T4, R'', margin=R''-W, ratio=W/R'';
answer: which term carries the margin; what is load-bearing on the tightest;
and whether W/(λ₂fᵀDf) or W/(λ₂(fᵀDf-λ₂)) is bounded by 1.

Run:  python conjecture_B_hard_regime.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def measure(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min()); Delta = float(d.max()); dbar = 2.0 * m / n
    S = float(d @ f); fDf = float((d * f * f).sum())
    Ln = nx.normalized_laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    mu2 = float(np.linalg.eigvalsh(Ln)[1])
    W = 0.0; SH = 0.0
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        w = min(d[i], d[j]) - delta
        if w > 0:
            W += w * (f[i] - f[j]) ** 2; SH += w
    T1 = l2 * fDf; T2 = -l2 * l2; T3 = l2; T4 = -l2 * S * S / m
    Rpp = T1 + T2 + T3 + T4
    return dict(n=n, m=m, Delta=Delta, delta=delta, dbar=dbar, l2=l2, mu2=mu2,
                fDf=fDf, S=S, SH=SH, W=W, T1=T1, T2=T2, T3=T3, T4=T4, Rpp=Rpp,
                margin=Rpp - W, ratio=(W / Rpp if Rpp > 1e-12 else np.nan),
                alpha=(W / (mu2 * fDf) if mu2 * fDf > 1e-12 else 0.0),
                cv2=float(np.var(d)) / dbar**2, ratioDd=Delta / delta)


def hard_graphs(target=50):
    """Large near-regular WS-type graphs, T(G)-connected, with α>1; take the
    ~target tightest by W/R''."""
    rng = np.random.default_rng(2026); cand = []
    seen = set()
    for _ in range(6000):
        n = int(rng.integers(20, 42)); k = int(rng.integers(6, min(18, n - 1)))
        p = float(rng.uniform(0.04, 0.45))
        G = nx.watts_strogatz_graph(n, k + (k % 2), p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T) or ce.lambda2(T) <= 1e-6:
            continue
        key = (n, G.number_of_edges(), nx.weisfeiler_lehman_graph_hash(G, iterations=2))
        if key in seen:
            continue
        seen.add(key)
        r = measure(G)
        # hard regime gate: near-regular, large, proxy fails
        if r["ratioDd"] <= 2.0 and r["alpha"] > 1.0 and r["n"] >= 20:
            cand.append((r, G))
    cand.sort(key=lambda rg: -rg[0]["ratio"])    # tightest lock first
    return cand[:target]


def main():
    hard = hard_graphs(50)
    rows = [r for r, _ in hard]
    N = len(rows)
    print(f"hard-regime graphs selected: {N} "
          f"(large near-regular WS, α>1, Δ/δ<=2)")
    if N == 0:
        return
    print(f"  n range {min(r['n'] for r in rows)}-{max(r['n'] for r in rows)}; "
          f"α range {min(r['alpha'] for r in rows):.2f}-{max(r['alpha'] for r in rows):.2f}; "
          f"W/R'' range {min(r['ratio'] for r in rows):.3f}-{max(r['ratio'] for r in rows):.3f}")

    # ===== sample table (tightest 12) =====
    print("\n--- tightest 12 (by W/R'') ---")
    print(f"{'n':>3s}{'m':>5s}{'λ₂':>7s}{'μ₂':>6s}{'fᵀDf':>8s}{'S':>7s}"
          f"{'W':>9s}{'T1=λ₂fDf':>10s}{'T2=-λ₂²':>9s}{'T3=+λ₂':>8s}{'T4':>7s}"
          f"{'R̈':>9s}{'marg':>8s}{'W/R̈':>6s}")
    for r in rows[:12]:
        print(f"{r['n']:>3d}{r['m']:>5d}{r['l2']:>7.3f}{r['mu2']:>6.3f}{r['fDf']:>8.3f}"
              f"{r['S']:>7.3f}{r['W']:>9.3f}{r['T1']:>10.2f}{r['T2']:>9.2f}{r['T3']:>8.3f}"
              f"{r['T4']:>7.3f}{r['Rpp']:>9.2f}{r['margin']:>8.2f}{r['ratio']:>6.3f}")

    # ===== Q1: where does the margin come from? =====
    print("\n=== Q1: which term provides the margin? ===")
    # mean fractional contribution of each term to R''
    for key, lab in [("T1", "λ₂·fᵀDf"), ("T2", "-λ₂²"), ("T3", "+λ₂ (the +1)"),
                     ("T4", "-λ₂·S²/m")]:
        frac = np.mean([r[key] / r["Rpp"] for r in rows])
        print(f"   {lab:14s}: mean term/R'' = {frac:+.3f}   "
              f"mean |term| = {np.mean([abs(r[key]) for r in rows]):.2f}")
    # how big is W relative to the cumulative sums?
    print("   --- W vs cumulative RHS pieces (fraction of graphs where W exceeds each) ---")
    exceed_T1 = np.mean([r["W"] > r["T1"] + 1e-7 for r in rows])
    exceed_12 = np.mean([r["W"] > r["T1"] + r["T2"] + 1e-7 for r in rows])  # λ₂(fDf-λ₂)
    exceed_124 = np.mean([r["W"] > r["T1"] + r["T2"] + r["T4"] + 1e-7 for r in rows])  # drop +1
    print(f"   W > T1 (=λ₂fᵀDf)             : {100*exceed_T1:.0f}%")
    print(f"   W > T1+T2 (=λ₂(fᵀDf-λ₂))     : {100*exceed_12:.0f}%   <- if high, the +λ₂ term is load-bearing")
    print(f"   W > T1+T2+T4 (drop the +1)   : {100*exceed_124:.0f}%   <- 'no +1' failure rate")
    # is S^2/m negligible (near-regular)?
    print(f"   mean S²/m = {np.mean([r['S']**2/r['m'] for r in rows]):.4f}  "
          f"(|T4|/R'' mean = {np.mean([abs(r['T4'])/r['Rpp'] for r in rows]):.4f})  -> correction negligible if ~0")

    # ===== Q2: tightest graph -- load-bearing term =====
    print("\n=== Q2: tightest graph (max W/R'') -- what breaks first? ===")
    rt = max(rows, key=lambda r: r["ratio"])
    print(f"   n={rt['n']} m={rt['m']} W={rt['W']:.3f} R''={rt['Rpp']:.3f} "
          f"W/R''={rt['ratio']:.4f} margin={rt['margin']:.3f}")
    print(f"   margin vs +λ₂ term: margin={rt['margin']:.3f}, T3=+λ₂={rt['T3']:.3f}  "
          f"-> {'+1 term IS load-bearing (margin<T3)' if rt['margin'] < rt['T3'] else 'margin>T3'}")
    # fraction of hard graphs where margin < λ₂ (the +1 alone carries the slack)
    lb = np.mean([r["margin"] < r["T3"] + 1e-9 for r in rows])
    print(f"   over hard regime: margin < +λ₂ on {100*lb:.0f}% (the +1 term carries the whole slack)")
    lb2 = np.mean([r["margin"] < abs(r["T2"]) for r in rows])
    print(f"   margin < λ₂² (=|T2|) on {100*lb2:.0f}% (margin is small vs the -λ₂² penalty)")

    # ===== Q3: are the two ratios bounded by 1? =====
    print("\n=== Q3: ratio bounds on the hard regime ===")
    r_a = np.array([r["W"] / r["T1"] for r in rows])                 # W/(λ₂fᵀDf)
    r_b = np.array([r["W"] / (r["T1"] + r["T2"]) for r in rows
                    if r["T1"] + r["T2"] > 1e-9])                    # W/(λ₂(fᵀDf-λ₂))
    print(f"   W/(λ₂·fᵀDf)        : max={r_a.max():.4f}  ({'<=1' if r_a.max()<=1+1e-6 else '>1!'})  "
          f"mean={r_a.mean():.4f}")
    print(f"   W/(λ₂·(fᵀDf-λ₂))   : max={r_b.max():.4f}  ({'<=1' if r_b.max()<=1+1e-6 else '>1 -> NOT bounded; +1 needed'})  "
          f"mean={r_b.mean():.4f}  (>1 on {100*np.mean(r_b>1+1e-6):.0f}%)")

    main.rows = rows


if __name__ == "__main__":
    main()
