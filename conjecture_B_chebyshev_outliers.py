"""
Conjecture B — profile the ~5% graphs where the Chebyshev bound on W fails.

Chebyshev sum bound:  CB = ΣH · Sg_up / m_up  (uphill edges).
Identity:  W - CB = m_up · Cov(w_e, g_e)  over uphill edges  (uniform weighting),
so  W > CB  ⟺  Cov(weight, gradient) > 0  ⟺  high-weight edges also carry high
gradient (the anticorrelation reverses).

Profiles every outlier: degree sequence, #distinct degrees, quasi-regularity,
λ₂ multiplicity, |Aut(G)|, vertex-transitivity; the breaking edges; ρ=W/ΣH vs λ₂;
and searches for a single structural predictor of failure.

Run:  python conjecture_B_chebyshev_outliers.py
"""
import numpy as np
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
import counterexample_search as ce

TOL = 1e-9
AUT_CAP = 200000


def edge_data(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); n = len(nodes); m = G.number_of_edges()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    delta = float(d.min())
    S = float(d @ f); fDf = float((d * f * f).sum())
    Rpp = l2 * (fDf - l2 + 1.0 - S * S / m)
    mult = int(np.sum(np.abs(ev - l2) < 1e-7))
    # uphill edges: weight w=min-δ, gradient g; record endpoint degrees, cut flag
    # Chebyshev over ALL positive-weight edges {min(d_a,d_b) > δ}, ties included
    # (tie edges with both endpoints above δ DO contribute to the lock W).
    W = 0.0; ws = []; gs = []; info = []
    for u, v in G.edges():
        i, j = idx[u], idx[v]
        w = min(d[i], d[j]) - delta
        if w <= 0:
            continue                              # zero-weight edge: no contribution
        g = (f[i] - f[j]) ** 2
        W += w * g
        ws.append(w); gs.append(g)
        info.append((w, g, int(d[i]), int(d[j]), f[i] * f[j] < 0))
    ws = np.array(ws); gs = np.array(gs); m_up = len(ws)
    SH = float(ws.sum()); Sg = float(gs.sum())
    CB = SH * Sg / m_up if m_up else 0.0
    cov = float(np.mean(ws * gs) - np.mean(ws) * np.mean(gs)) if m_up else 0.0
    corr = (float(np.corrcoef(ws, gs)[0, 1])
            if m_up >= 3 and np.std(ws) > 1e-12 and np.std(gs) > 1e-12 else np.nan)
    rho = W / SH if SH > 1e-12 else np.nan
    return dict(n=n, m=m, d=d, delta=delta, Delta=float(d.max()), l2=l2, mult=mult,
                fDf=fDf, Rpp=Rpp, W=W, CB=CB, SH=SH, Sg=Sg, m_up=m_up,
                cov=cov, corr=corr, rho=rho, info=info,
                outlier=(W > CB + 1e-9), lock_ok=(W <= Rpp + 1e-7))


def structural(G, r):
    d = r["d"]
    degseq = sorted((int(x) for x in d), reverse=True)
    ndist = len(set(degseq))
    quasireg = (r["Delta"] - r["delta"]) <= 2
    # automorphisms (capped)
    autos = []
    gm = GraphMatcher(G, G)
    for i, iso in enumerate(gm.isomorphisms_iter()):
        autos.append(iso)
        if i + 1 >= AUT_CAP:
            break
    aut_size = len(autos)
    capped = aut_size >= AUT_CAP
    # vertex-transitive: single orbit under the (capped) automorphisms
    nodes = list(G.nodes())
    orbit0 = set()
    for iso in autos:
        orbit0.add(iso[nodes[0]])
    vt = (len(orbit0) == len(nodes)) and not capped
    return dict(degseq=degseq, ndist=ndist, quasireg=quasireg,
                aut=("%d%s" % (aut_size, "+" if capped else "")), vt=vt,
                spread=int(r["Delta"] - r["delta"]))


def datasets():
    import conjecture_B_proof_v4_explore as v4
    tight = [G for _, G in v4.tight_graphs()]
    broad = [G for _, G in v4.broad_graphs(1500)]
    rng = np.random.default_rng(99); dense = []; seen = set()
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
    out = {}
    for k, gs in (("tight", tight), ("broad", broad), ("dense", dense)):
        out[k] = [G for G in gs if keep(G)]
    return out


def main():
    ds = datasets()
    all_rows = []; outliers = []
    for k, gs in ds.items():
        for G in gs:
            r = edge_data(G); r["set"] = k; r["G"] = G
            all_rows.append(r)
            if r["outlier"] and r["l2"] > 1e-9:
                outliers.append(r)

    N = len(all_rows); nout = len(outliers)
    print(f"total graphs: {N}   Chebyshev-failure outliers (W>CB): {nout} ({100*nout/N:.1f}%)")

    # add structural profile to outliers
    for r in outliers:
        r.update(structural(r["G"], r))

    # ---- aggregate: outliers vs rest ----
    rest = [r for r in all_rows if not r["outlier"] and r["l2"] > 1e-9]
    def m(rows, key):
        vals = [x[key] for x in rows if x.get(key) == x.get(key)]
        return float(np.mean(vals)) if vals else float("nan")
    print("\n--- outliers vs rest (means) ---")
    print(f"  degree spread Δ-δ : outliers={np.mean([r['spread'] for r in outliers]):.2f}  "
          f"rest={np.mean([r['Delta']-r['delta'] for r in rest]):.2f}")
    print(f"  #distinct degrees : outliers={np.mean([r['ndist'] for r in outliers]):.2f}  "
          f"rest={np.mean([len(set(r['d'])) for r in rest]):.2f}")
    print(f"  quasi-regular (Δ-δ<=2): outliers={np.mean([r['quasireg'] for r in outliers]):.2f}  "
          f"rest={np.mean([(r['Delta']-r['delta'])<=2 for r in rest]):.2f}")
    print(f"  λ₂ multiplicity   : outliers={m(outliers,'mult'):.2f}  rest={m(rest,'mult'):.2f}")
    print(f"  vertex-transitive : outliers={np.mean([r['vt'] for r in outliers]):.2f}")

    # ---- ρ on outliers vs rest ----
    ro = np.array([r["rho"]/r["l2"] for r in outliers if r["rho"]==r["rho"]])
    rr = np.array([r["rho"]/r["l2"] for r in rest if r["rho"]==r["rho"]])
    print("\n--- ρ/λ₂ ---")
    print(f"  outliers: max={ro.max():.4f} median={np.median(ro):.4f}")
    print(f"  rest    : max={rr.max():.4f} median={np.median(rr):.4f}")
    # still ≤ R''/ΣH (lock) on outliers?
    print(f"  lock W<=R'' on outliers: {sum(1 for r in outliers if r['lock_ok'])}/{nout}")

    # ---- breaking edges: among outliers, the high-weight & high-gradient edges ----
    print("\n--- breaking edges (high weight AND high gradient) on outliers ---")
    same_hi = 0; tot_break = 0; cut_break = 0
    for r in outliers:
        if r["m_up"] < 2:
            continue
        ws = np.array([t[0] for t in r["info"]]); gs = np.array([t[1] for t in r["info"]])
        wmed = np.median(ws); gmed = np.median(gs)
        for (w, g, da, db, iscut) in r["info"]:
            if w >= wmed and g >= gmed and w > 0:
                tot_break += 1
                if abs(da - db) <= 1:           # endpoints of similar (high) degree
                    same_hi += 1
                if iscut:
                    cut_break += 1
    print(f"  breaking edges total: {tot_break}; between similar-degree (|da-db|<=1): "
          f"{same_hi} ({100*same_hi/max(tot_break,1):.0f}%); sign-cut: {cut_break} "
          f"({100*cut_break/max(tot_break,1):.0f}%)")

    # ---- distribution of #distinct degrees among outliers ----
    from collections import Counter
    cnt = Counter(r["ndist"] for r in outliers)
    print(f"\n--- #distinct-degree-classes among outliers: {dict(sorted(cnt.items()))}")
    cntsp = Counter(r["spread"] for r in outliers)
    print(f"--- degree-spread Δ-δ among outliers: {dict(sorted(cntsp.items()))}")

    # ---- a few example outliers ----
    print("\n--- sample outliers ---")
    for r in sorted(outliers, key=lambda x: -x["rho"]/x["l2"])[:8]:
        print(f"  set={r['set']:5s} n={r['n']} m={r['m']} Δ-δ={r['spread']} ndist={r['ndist']} "
              f"mult={r['mult']} vt={r['vt']} aut={r['aut']:>7s} "
              f"ρ/λ₂={r['rho']/r['l2']:.3f} corr(w,g)={r['corr']:+.2f} degseq={r['degseq'][:8]}")

    main.outliers = outliers; main.all_rows = all_rows


if __name__ == "__main__":
    main()
