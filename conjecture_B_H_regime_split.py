"""
Two-regime proof attempt for  C+R'' >= 0  split by  H(f)=Σ f_v²/d_v  (corr -0.935).
Logic: R''>=0 always, so C+R''>=0 is automatic when C>=0; the hard case is C<0, where
we need R'' >= |C|.
  Regime 1 (H small): fᵀDf>=1/H large -> R'' large; try crude bound |C| <= B <= R''.
  Regime 2 (H large): Fiedler on low/equal-degree vertices -> C ~ 0.
Task 7: C=0 when degrees are equal on every support-incident edge (Lean-ready lemma).
Run:  python conjecture_B_H_regime_split.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-7


def data(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    ev, V = np.linalg.eigh(L); l2 = float(ev[1])
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    H = float(np.sum(f * f / d))
    C = 0.0
    sumf_h2 = 0.0; cs_grad = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        h, lo = (i, j) if d[i] >= d[j] else (j, i)
        C += (d[h] - d[lo]) * f[h] * (f[h] - f[lo])
        sumf_h2 += f[h] ** 2
        cs_grad += (d[h] - d[lo]) ** 2 * (f[h] - f[lo]) ** 2
    # support-incidence test for Task 7
    supp = np.abs(f) > TOL
    homog = True
    for u, v in edges:
        i, j = idx[u], idx[v]
        if (supp[i] or supp[j]) and d[i] != d[j]:
            homog = False
            break
    # crude C-S bound on |C|: |C| <= sqrt(Σ(Δd)²(Δf)²) * sqrt(Σ f_h²)
    Cb_cs = np.sqrt(cs_grad) * np.sqrt(sumf_h2)
    dmax = float(d.max())
    return dict(n=n, m=m, l2=l2, H=H, C=C, Rpp=Rpp, target=C + Rpp, fDf=fDf,
                dmax=dmax, homog=homog, Cb_cs=Cb_cs, absC=abs(C))


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
    rows = [data(G) for G in corpus(9)]
    rows = [r for r in rows if r["l2"] > 1e-6]
    N = len(rows)
    H = np.array([r["H"] for r in rows])
    C = np.array([r["C"] for r in rows])
    Rpp = np.array([r["Rpp"] for r in rows])
    tgt = np.array([r["target"] for r in rows])
    print(f"corpus: {N} graphs;  corr(H, C+R'')={np.corrcoef(H,tgt)[0,1]:+.3f}")

    # ---- the real difficulty is C<0 ----
    negC = C < -1e-9
    print(f"\nC>=0 (trivial, since R''>=0): {int(np.sum(~negC))}/{N};  "
          f"C<0 (hard, need R''>=|C|): {int(np.sum(negC))}/{N}")

    # ---- Task 7: C=0 when degrees equal on support-incident edges ----
    print("\n===== TASK 7: C=0 on support-degree-homogeneous graphs =====")
    homog = np.array([r["homog"] for r in rows])
    maxC_homog = max((abs(r["C"]) for r in rows if r["homog"]), default=0.0)
    print(f"  graphs with d_a=d_b on every supp-incident edge: {int(homog.sum())}/{N}")
    print(f"  max |C| among them: {maxC_homog:.2e}  => C=0 holds: {maxC_homog < 1e-7}")

    # ---- sign of C vs H ----
    print("\n===== sign of C across H bins =====")
    print("  H bin        | #graphs | frac C>=0 | frac C<0 | median |C|/R'' | max |C|/R''")
    bins = [(0, 0.20), (0.20, 0.25), (0.25, 0.30), (0.30, 0.35), (0.35, 0.45), (0.45, 0.51)]
    ratioCR = np.abs(C) / np.maximum(Rpp, 1e-12)
    for lo, hi in bins:
        m = (H >= lo) & (H < hi)
        if m.sum():
            print(f"  [{lo:.2f},{hi:.2f}) | {int(m.sum()):7d} | {np.mean(C[m]>=-1e-9):8.3f}  | "
                  f"{np.mean(C[m]<-1e-9):8.3f} | {np.median(ratioCR[m]):13.4f} | {ratioCR[m].max():.4f}")

    # ---- REGIME 1: crude C-S bound on |C| vs R'' (small H) ----
    print("\n===== REGIME 1: crude C-S bound  |C| <= Cb_cs;  is Cb_cs <= R''? =====")
    Cb = np.array([r["Cb_cs"] for r in rows])
    absC = np.abs(C)
    print(f"  |C| <= Cb_cs (C-S) holds: {int(np.sum(absC <= Cb + 1e-9))}/{N}")
    cs_le_R = Cb <= Rpp + 1e-9
    print(f"  Cb_cs <= R'' holds: {int(np.sum(cs_le_R))}/{N} ({100*np.mean(cs_le_R):.1f}%)")
    # where does the crude chain Cb_cs <= R'' hold, by H?
    for lo, hi in bins:
        m = (H >= lo) & (H < hi)
        if m.sum():
            print(f"    H[{lo:.2f},{hi:.2f}): Cb_cs<=R'' on {100*np.mean(cs_le_R[m]):5.1f}%  "
                  f"(median Cb_cs/R''={np.median(Cb[m]/np.maximum(Rpp[m],1e-12)):.2f})")

    # ---- COMBINED: threshold c ----
    print("\n===== COMBINED threshold search =====")
    # Regime 1 provable if Cb_cs<=R'' (then |C|<=Cb_cs<=R'' => C+R''>=0).
    # Regime 2 trivial if C>=0.
    # A graph is COVERED if (Cb_cs<=R'') OR (C>=0).
    covered = cs_le_R | (~negC)
    print(f"  covered by [Regime1: Cb_cs<=R''] OR [Regime2: C>=0]: "
          f"{int(np.sum(covered))}/{N} ({100*np.mean(covered):.2f}%)")
    if np.sum(~covered):
        unc = [rows[k] for k in range(N) if not covered[k]]
        Hunc = np.array([r["H"] for r in unc])
        print(f"  UNCOVERED: {len(unc)} graphs; their H: min={Hunc.min():.3f} "
              f"median={np.median(Hunc):.3f} max={Hunc.max():.3f}")
        print(f"    these have C<0 AND crude C-S too weak — the genuine hard core")
        worst = max(unc, key=lambda r: abs(r["C"]) / max(r["Rpp"], 1e-12))
        print(f"    worst |C|/R''={abs(worst['C'])/worst['Rpp']:.4f} at n={worst['n']} "
              f"m={worst['m']} H={worst['H']:.3f}")

    # threshold c where C>=0 takes over (regime 2)
    print("\n  fraction C>=0 above H-threshold c:")
    for c in (0.30, 0.33, 0.35, 0.38, 0.40):
        m = H > c
        if m.sum():
            print(f"    H>{c}: {int(m.sum())} graphs, frac C>=0 = {np.mean(C[m]>=-1e-9):.3f}, "
                  f"max|C|/R''={ratioCR[m].max():.3f}")


if __name__ == "__main__":
    main()
