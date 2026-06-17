"""
Empirical test of the harmonic-mass quantity  H(f) = Σ_v f_v² / d_v  (f = unit Fiedler).
Also H(u_k) for higher eigenvectors, and the Cauchy-Schwarz identity H(f)·fᵀDf ≥ 1.
Run:  python harmonic_mass_test.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def Hf(d, f):
    return float(np.sum(f * f / d))


def data(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1])
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    C = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        h, lo = (i, j) if d[i] >= d[j] else (j, i)
        C += (d[h] - d[lo]) * f[h] * (f[h] - f[lo])
    H = Hf(d, f)
    return dict(n=n, m=m, l2=l2, H=H, fDf=fDf, target=C + Rpp,
                HfDf=H * fDf, reg=(d.std() < 1e-9), dmin=int(d.min()), dmax=int(d.max()))


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
    rows = []
    for G in graphs:
        r = data(G)
        if r["l2"] > 1e-6:
            r["G"] = G
            rows.append(r)
    N = len(rows)
    H = np.array([r["H"] for r in rows])
    print(f"corpus: {N} distinct graphs")

    # 1. violations
    nv = int(np.sum(H > 1 + 1e-9))
    print(f"\n[1] H(f) ≤ 1 : violations {nv}/{N}  (max H = {H.max():.6f})")

    # 2. distribution
    print(f"[2] H(f): min={H.min():.4f} median={np.median(H):.4f} mean={H.mean():.4f} max={H.max():.6f}")

    # 3. closest to 1
    order = np.argsort(-H)
    print("[3] closest to 1 (top 12):")
    for k in order[:12]:
        r = rows[k]
        fam = "regular" if r["reg"] else f"d∈[{r['dmin']},{r['dmax']}]"
        print(f"     H={r['H']:.5f}  n={r['n']} m={r['m']} λ₂={r['l2']:.3f} {fam}")

    # 4. equality
    eq = [r for r in rows if r["H"] > 1 - 1e-6]
    print(f"[4] equality H=1 (within 1e-6): {len(eq)} graphs")
    for r in eq[:10]:
        print(f"     n={r['n']} m={r['m']} reg={r['reg']} "
              f"K_n?={'yes' if r['m']==r['n']*(r['n']-1)//2 else 'no'}")
    # are equality graphs exactly complete?
    nKn = sum(1 for r in eq if r["m"] == r["n"] * (r["n"] - 1) // 2)
    print(f"     of which complete graphs K_n: {nKn}/{len(eq)}")

    # 5. correlation with B slack
    tgt = np.array([r["target"] for r in rows])
    print(f"[5] corr(H(f), C+R'') = {np.corrcoef(H, tgt)[0,1]:+.3f}")

    # 6. Cauchy-Schwarz identity H·fDf ≥ 1
    HfDf = np.array([r["HfDf"] for r in rows])
    print(f"[6] H(f)·fᵀDf ≥ 1 : holds {int(np.sum(HfDf >= 1 - 1e-9))}/{N}; "
          f"min={HfDf.min():.5f} (equality ⟺ regular)")
    # check equality cases of CS are regular graphs
    cseq = [r for r in rows if r["HfDf"] < 1 + 1e-6]
    print(f"     H·fDf = 1 (within 1e-6): {len(cseq)} graphs, all regular: "
          f"{all(r['reg'] for r in cseq)}")

    # higher eigenvectors
    print("\n[higher] H(u_k) for k=2..6 (1-indexed Fiedler=u_2), subsample 800:")
    sub = graphs[:800]
    perk = {k: [] for k in range(1, 7)}
    viol = {k: 0 for k in range(1, 7)}
    for G in sub:
        nodes = list(G.nodes()); n = len(nodes)
        L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
        d = L.diagonal()
        if d.min() <= 0:
            continue
        ev, Vv = np.linalg.eigh(L)
        if ev[1] < 1e-6:
            continue
        for k in range(1, min(7, n)):       # index 1=Fiedler, 2=u_3, ...
            uk = Vv[:, k] / np.linalg.norm(Vv[:, k])
            h = Hf(d, uk)
            perk[k].append(h)
            if h > 1 + 1e-9:
                viol[k] += 1
    for k in range(1, 7):
        if perk[k]:
            a = np.array(perk[k])
            label = "u_2(Fiedler)" if k == 1 else f"u_{k+1}"
            print(f"     {label:13s}: max={a.max():.4f} median={np.median(a):.4f} "
                  f"viol(>1)={viol[k]}/{len(a)}")


if __name__ == "__main__":
    main()
