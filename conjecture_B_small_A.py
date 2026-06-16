"""
Conjecture B — the residual small-A regime  A = fᵀDf − λ₂ < 3/2.

Lock:  W ≤ R'' = λ₂(A + 1 − S²/m).  Candidate residual lemmas (bound | implies B?):
  L1  W ≤ λ₂                       implies B iff A ≥ S²/m
  L2  W ≤ λ₂(1 − S²/m)             implies B always (≤ R'' since A≥0)
  L3  W ≤ λ₂(A + 1 − S²/m) = R''   (the lock itself)
  L4  W ≤ λ₂(δ − λ₂ + 1 − S²/m)    implies B always (δ ≤ fᵀDf ⇒ ≤ R''); 'C4'
  L5  W ≤ λ₂(2 − λ₂/δ)             implies B iff ≤ R'' (tested)

Enumerate A<3/2 graphs, classify, test each lemma (holds + implies-B), pick the
weakest TRUE lemma that implies B.

Run:  python conjecture_B_small_A.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def measure(G, tag):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min()); Delta = float(d.max())
    S = float(d @ f); fDf = float((d * f * f).sum()); A = fDf - l2
    S2m = S * S / m
    Rpp = l2 * (A + 1.0 - S2m)
    W = 0.0
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        w = min(d[i], d[j]) - delta
        if w > 0:
            W += w * (f[i] - f[j]) ** 2
    return dict(tag=tag, n=n, m=m, delta=delta, Delta=Delta, l2=l2, fDf=fDf, A=A,
                S=S, S2m=S2m, W=W, Rpp=Rpp,
                density=m / (n * (n - 1) / 2.0), l2_over_delta=l2 / delta,
                WR=(W / Rpp if Rpp > 1e-12 else np.nan),
                degseq=sorted((int(x) for x in d), reverse=True))


def corpus():
    rows = []
    for n in range(6, 14):
        K = nx.complete_graph(n); E = list(K.edges())
        for k in range(1, 8):
            G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E[k:])
            rows.append(("Kminus", G))
        G = nx.complete_graph(n)
        for j in range(2, n): G.remove_edge(0, j)
        rows.append(("Kstar", G))
    for parts in ([4,3],[5,3],[4,4,1],[5,2,2],[3,3,2],[6,3],[4,3,2],[5,4],[6,4],[7,3],
                  [8,2],[5,5],[6,5]):
        rows.append(("Kmulti", nx.complete_multipartite_graph(*parts)))
    rng = np.random.default_rng(31); seen = set()
    for _ in range(4000):
        n = int(rng.integers(8, 18)); p = float(rng.uniform(0.3, 0.97))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if nx.is_connected(G): rows.append(("gnp", G))
    for _ in range(3000):
        n = int(rng.integers(14, 40)); k = int(rng.integers(6, min(18, n - 1)))
        p = float(rng.uniform(0.04, 0.5))
        rows.append(("WS", nx.watts_strogatz_graph(n, k + (k % 2), p, seed=int(rng.integers(0, 2**31)))))
    out = []
    for tag, G in rows:
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() >= 2 and nx.is_connected(T) and ce.lambda2(T) > 1e-6:
            key = (tag, G.number_of_nodes(), G.number_of_edges(),
                   nx.weisfeiler_lehman_graph_hash(G, iterations=2))
            if key not in seen:
                seen.add(key); out.append((tag, G))
    return out


def classify(r):
    if r["density"] >= 0.75:
        return "near-complete"
    if r["density"] < 0.45 and r["l2"] < 2.5:
        return "sparse-low-λ₂"
    return "intermediate"


def main():
    allrows = [measure(G, tag) for tag, G in corpus()]
    allrows = [r for r in allrows if r["A"] > 1e-9 and r["l2"] > 1e-6]
    small = [r for r in allrows if r["A"] < 1.5]
    N = len(small)
    print(f"corpus: {len(allrows)} ; small-A (A<3/2): {N}")

    # ---- classification ----
    from collections import Counter
    cls = Counter(classify(r) for r in small)
    print(f"\nclassification: {dict(cls)}")
    tags = Counter(r["tag"] for r in small)
    print(f"by family: {dict(tags)}")
    print(f"density: min={min(r['density'] for r in small):.2f} "
          f"median={np.median([r['density'] for r in small]):.2f} "
          f"max={max(r['density'] for r in small):.2f}")
    print(f"λ₂/δ: min={min(r['l2_over_delta'] for r in small):.3f} "
          f"median={np.median([r['l2_over_delta'] for r in small]):.3f} "
          f"max={max(r['l2_over_delta'] for r in small):.3f}")
    print(f"S²/m: median={np.median([r['S2m'] for r in small]):.4f} "
          f"max={max(r['S2m'] for r in small):.4f}")
    print(f"W/R'': median={np.median([r['WR'] for r in small]):.3f} "
          f"max={max(r['WR'] for r in small):.3f}")

    # ---- sample table by class ----
    print("\nsample (3 per class):")
    print(f"   {'class':14s}{'tag':7s}{'n':>3s}{'m':>5s}{'dens':>6s}{'δ':>4s}{'Δ':>4s}"
          f"{'λ₂':>7s}{'λ₂/δ':>6s}{'A':>6s}{'S²/m':>7s}{'W':>8s}{'R̈':>8s}{'W/R̈':>6s}")
    bycls = {}
    for r in small:
        bycls.setdefault(classify(r), []).append(r)
    for c, rs in bycls.items():
        for r in sorted(rs, key=lambda r: -r["WR"])[:3]:
            print(f"   {c:14s}{r['tag']:7s}{r['n']:>3d}{r['m']:>5d}{r['density']:>6.2f}"
                  f"{int(r['delta']):>4d}{int(r['Delta']):>4d}{r['l2']:>7.3f}"
                  f"{r['l2_over_delta']:>6.3f}{r['A']:>6.3f}{r['S2m']:>7.3f}"
                  f"{r['W']:>8.3f}{r['Rpp']:>8.3f}{r['WR']:>6.3f}")

    # ---- candidate lemmas ----
    print("\n=== candidate residual lemmas (over %d small-A graphs) ===" % N)
    cands = [
        ("L1: λ₂",                 lambda r: r["l2"]),
        ("L2: λ₂(1−S²/m)",         lambda r: r["l2"] * (1 - r["S2m"])),
        ("L3: λ₂(A+1−S²/m)=R''",   lambda r: r["Rpp"]),
        ("L4: λ₂(δ−λ₂+1−S²/m)",    lambda r: r["l2"] * (r["delta"] - r["l2"] + 1 - r["S2m"])),
        ("L5: λ₂(2−λ₂/δ)",         lambda r: r["l2"] * (2 - r["l2"] / r["delta"])),
    ]
    results = []
    for name, fn in cands:
        holds = sum(1 for r in small if r["W"] <= fn(r) + 1e-7)
        implB = sum(1 for r in small if fn(r) <= r["Rpp"] + 1e-7)
        both = sum(1 for r in small if r["W"] <= fn(r) + 1e-7 and fn(r) <= r["Rpp"] + 1e-7)
        mx = max((r["W"] / fn(r)) for r in small if fn(r) > 1e-12)
        results.append((name, holds, implB, both, mx))
        print(f"   {name:26s}: holds {holds}/{N} ({100*holds/N:.0f}%) | "
              f"implies-B {implB}/{N} ({100*implB/N:.0f}%) | both {both}/{N} | max W/bound={mx:.3f}")

    # ---- weakest TRUE B-implying lemma ----
    print("\n=== weakest TRUE lemma that implies B in small-A ===")
    # among lemmas with holds=100% AND implies-B=100%, pick the one with LARGEST RHS
    # (weakest). Compare mean RHS.
    valid = [(name, fn) for (name, fn), (nm, h, ib, b, mx) in zip(cands, results)
             if h == N and ib == N]
    if valid:
        # larger mean bound = weaker
        valid_sorted = sorted(valid, key=lambda nf: -np.mean([nf[1](r) for r in small]))
        print("   lemmas that are 100% true AND 100% imply-B (weakest first by mean RHS):")
        for name, fn in valid_sorted:
            print(f"     {name}  (mean RHS={np.mean([fn(r) for r in small]):.3f})")
        print(f"\n   -> WEAKEST TRUE B-IMPLYING: {valid_sorted[0][0]}")
    else:
        print("   none of L1,L2,L4,L5 is simultaneously 100%-true and 100%-imply-B;")
        print("   only L3 (=R'', the lock) qualifies trivially.")
        # report which fail and how
        for (name, fn), (nm, h, ib, b, mx) in zip(cands, results):
            if name.startswith("L3"):
                continue
            fail_hold = N - h; fail_impl = N - ib
            print(f"     {name}: {fail_hold} hold-failures, {fail_impl} imply-B-failures")

    main.small = small; main.results = results


if __name__ == "__main__":
    main()
