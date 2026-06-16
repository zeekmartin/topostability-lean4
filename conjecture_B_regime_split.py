"""
Conjecture B — two-regime proof strategy.  A := fᵀDf - λ₂  (≥ 0 always).

Lock:  W ≤ R'' = λ₂(A + 1 - S²/m),  S = Σ d_v f_v.

GLOBAL candidates (want: W ≤ bound holds 100% AND bound ≤ R'' so it implies B):
  C1  W ≤ λ₂·max(A,1)      (= regime split at c=1)
  C2  W ≤ λ₂·(A+1)         (R'' with S²/m dropped; NOTE: weaker than lock -> holds
                            trivially if lock holds, but does NOT imply B)
  C3  W ≤ λ₂·A             (strong; implies B when S²/m≤1; may fail on near-complete)

REGIME SPLIT: for c, large-A (A≥c): W≤λ₂A ; small-A (A<c): W≤λ₂.  Find clean c.

KEY DIAGNOSTIC: distribution of W/(λ₂·A) over all graphs; max + argmax graph.

Run:  python conjecture_B_regime_split.py
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
    S = float(d @ f); fDf = float((d * f * f).sum())
    A = fDf - l2
    Rpp = l2 * (A + 1.0 - S * S / m)
    W = 0.0
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        w = min(d[i], d[j]) - delta
        if w > 0:
            W += w * (f[i] - f[j]) ** 2
    return dict(tag=tag, n=n, m=m, Delta=Delta, delta=delta, l2=l2, fDf=fDf, A=A,
                S=S, W=W, Rpp=Rpp, S2m=S * S / m,
                degseq=sorted((int(x) for x in d), reverse=True))


def corpus():
    rows = []
    # near-complete (small-A regime): K_n minus k edges / star deletions
    for n in range(6, 14):
        K = nx.complete_graph(n); E = list(K.edges())
        for k in range(1, 7):
            G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E[k:])
            rows.append(("Kminus", G))
        G = nx.complete_graph(n)
        for j in range(2, n): G.remove_edge(0, j)
        rows.append(("Kstar", G))
    # complete multipartite
    for parts in ([4,3],[5,3],[4,4,1],[5,2,2],[3,3,2],[6,3],[4,3,2],[5,4],[6,4],[7,3]):
        rows.append(("Kmulti", nx.complete_multipartite_graph(*parts)))
    rng = np.random.default_rng(31); seen = set()
    # dense gnp
    for _ in range(1200):
        n = int(rng.integers(8, 16)); p = float(rng.uniform(0.4, 0.95))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if nx.is_connected(G): rows.append(("gnp", G))
    # WS hard regime (large near-regular)
    for _ in range(2500):
        n = int(rng.integers(14, 40)); k = int(rng.integers(6, min(18, n - 1)))
        p = float(rng.uniform(0.04, 0.45))
        rows.append(("WS", nx.watts_strogatz_graph(n, k + (k % 2), p, seed=int(rng.integers(0, 2**31)))))
    # filter to T(G)-connected
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


def main():
    rows = [measure(G, tag) for tag, G in corpus()]
    rows = [r for r in rows if r["A"] > 1e-9 and r["l2"] > 1e-6]
    N = len(rows)
    print(f"corpus (T(G)-connected, A>0): {N} graphs")
    lock = sum(1 for r in rows if r["W"] <= r["Rpp"] + 1e-7)
    print(f"lock W<=R'' holds: {lock}/{N}")

    # ===== GLOBAL candidates =====
    def report(name, bound_fn):
        ratios = np.array([r["W"] / bound_fn(r) for r in rows if bound_fn(r) > 1e-12])
        impl = np.mean([bound_fn(r) <= r["Rpp"] + 1e-7 for r in rows]) * 100   # bound<=R'' (implies B)
        viol = int(np.sum(ratios > 1 + 1e-7))
        return ratios.max(), viol, impl
    print("\n=== GLOBAL candidates (max W/bound ; #violations ; %% bound<=R'' implies-B) ===")
    for name, fn in [
        ("C1: λ₂·max(A,1)", lambda r: r["l2"] * max(r["A"], 1.0)),
        ("C2: λ₂·(A+1)   ", lambda r: r["l2"] * (r["A"] + 1.0)),
        ("C3: λ₂·A       ", lambda r: r["l2"] * r["A"]),
    ]:
        mx, viol, impl = report(name, fn)
        verdict = "HOLDS 100%" if viol == 0 else f"{viol} violations"
        print(f"   {name}: max W/bound={mx:.4f}  [{verdict}]  bound<=R'' on {impl:.0f}%")

    # ===== KEY DIAGNOSTIC: W/(λ₂·A) =====
    print("\n=== KEY DIAGNOSTIC: W/(λ₂·A) ===")
    wla = np.array([r["W"] / (r["l2"] * r["A"]) for r in rows])
    amax = max(rows, key=lambda r: r["W"] / (r["l2"] * r["A"]))
    print(f"   max W/(λ₂·A) = {wla.max():.4f}  (>1 means C3 fails)")
    print(f"   achieved by: tag={amax['tag']} n={amax['n']} m={amax['m']} A={amax['A']:.3f} "
          f"λ₂={amax['l2']:.3f} W={amax['W']:.3f}  degseq={amax['degseq'][:10]}")
    print(f"   mean={wla.mean():.4f}  median={np.median(wla):.4f}")
    # histogram
    bins = [0, 0.25, 0.5, 0.75, 1.0, 1.5, 2.0, 5.0, 1e9]
    labels = ["[0,.25)", "[.25,.5)", "[.5,.75)", "[.75,1)", "[1,1.5)", "[1.5,2)", "[2,5)", "[5,∞)"]
    hist = np.histogram(wla, bins=bins)[0]
    print("   histogram of W/(λ₂·A):")
    for lab, c in zip(labels, hist):
        bar = "#" * int(60 * c / max(hist.max(), 1))
        print(f"     {lab:9s} {c:5d} {bar}")
    # which tags are the >1 ones?
    over = [r for r in rows if r["W"] > r["l2"] * r["A"] + 1e-7]
    from collections import Counter
    print(f"   graphs with W>λ₂·A: {len(over)}  by family: {dict(Counter(r['tag'] for r in over))}")
    print(f"     their A: min={min(r['A'] for r in over):.3f} max={max(r['A'] for r in over):.3f} "
          f"median={np.median([r['A'] for r in over]):.3f}")

    # ===== REGIME SPLIT sweep =====
    print("\n=== REGIME SPLIT: large-A (A≥c): W≤λ₂A ; small-A (A<c): W≤λ₂ ===")
    for c in [0.1, 0.5, 1.0, 1.5, 2.0]:
        vL = vS = nL = nS = 0
        implL = implS = 0
        for r in rows:
            if r["A"] >= c:
                nL += 1
                if r["W"] > r["l2"] * r["A"] + 1e-7: vL += 1
                if r["l2"] * r["A"] <= r["Rpp"] + 1e-7: implL += 1
            else:
                nS += 1
                if r["W"] > r["l2"] + 1e-7: vS += 1
                if r["l2"] <= r["Rpp"] + 1e-7: implS += 1
        tot_v = vL + vS
        print(f"   c={c:>4.1f}: large-A {nL} graphs ({vL} viol, λ₂A<=R'' {100*implL/max(nL,1):.0f}%) | "
              f"small-A {nS} graphs ({vS} viol, λ₂<=R'' {100*implS/max(nS,1):.0f}%) | "
              f"TOTAL viol {tot_v} {'<- CLEAN' if tot_v==0 else ''}")

    main.rows = rows


if __name__ == "__main__":
    main()
