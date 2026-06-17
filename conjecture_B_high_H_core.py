"""
Focus on the uncovered 9% hard core (H high, C<0, crude CS fails, |C|/R''<=0.26).
Find a sharper bound on |C| that is <= R'' there.

C = Σ_{ab}(d_h-d_l) f_h (f_h-f_l)  (h=higher-degree endpoint).  R''=λ₂(fᵀDf-λ₂+1-S²/m).
Hard core := {C < 0  AND  Cb_cs > R''}  (Cb_cs = original Cauchy-Schwarz bound).
Run:  python conjecture_B_high_H_core.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def analyse(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); l2 = float(ev[1])
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    H = float(np.sum(f * f / d))
    Ad = A @ d
    # per-edge oriented data
    C = 0.0
    cs_grad = 0.0; sum_fh2 = 0.0       # original CS pieces
    hub = 0.0                          # (a) hub-flatness bound
    w1a = 0.0; w1b = 0.0               # (c) w=d_h-d_l
    wma = 0.0; wmb = 0.0               # (c) w=d_l-1
    wha = 0.0; whb = 0.0               # (c) w=1/(d_h-λ₂)²
    gpos = np.zeros(n)                 # (d) inner sums per high endpoint
    contrib = []                       # (edge contribution, dh, dl, fh, fl)
    for u, v in edges:
        i, j = idx[u], idx[v]
        if d[i] >= d[j]:
            h, lo = i, j
        else:
            h, lo = j, i
        dh, dl = d[h], d[lo]; fh, fl = f[h], f[lo]
        term = (dh - dl) * fh * (fh - fl)
        C += term
        contrib.append((term, dh, dl, fh, fl, abs(dh - dl)))
        cs_grad += (dh - dl) ** 2 * (fh - fl) ** 2
        sum_fh2 += fh ** 2
        # (a) hub-flatness: |f_h| <= sqrt(dh)/(dh-λ₂) =: Bh   (dh>λ₂ assumed)
        Bh = np.sqrt(dh) / (dh - l2) if dh - l2 > 1e-9 else abs(fh)
        Bh = max(Bh, abs(fh))
        hub += (dh - dl) * Bh * (Bh + abs(fl))
        # (c) weighted CS pieces  |C| <= sqrt(Σ w (Δf)²) sqrt(Σ (Δd)² fh² / w)
        df2 = (fh - fl) ** 2; dd = dh - dl
        if dd > 1e-9:
            w1a += dd * df2;            w1b += dd * fh ** 2
            wma += (dl - 1) * df2;      wmb += dd ** 2 * fh ** 2 / max(dl - 1, 1e-9)
            wh = 1.0 / (dh - l2) ** 2 if dh - l2 > 1e-9 else 1.0
            wha += wh * df2;            whb += dd ** 2 * fh ** 2 / wh
        # (d) inner sum at high endpoint h
        gpos[h] += (dh - dl) * (fh - fl)
    Cb_cs = np.sqrt(cs_grad) * np.sqrt(sum_fh2)
    Cb_w1 = np.sqrt(w1a) * np.sqrt(w1b)
    Cb_wmin = np.sqrt(wma) * np.sqrt(wmb)
    Cb_whub = np.sqrt(wha) * np.sqrt(whb)
    Cb_pv = float(np.sum(np.abs(f) * np.abs(gpos)))
    # (b) exact algebra: C = ½E_grad - ½E_disc ; when C<0, |C| = ½(E_disc-E_grad) <= ½E_disc
    Edisc = float((f * f) @ (Ad - d * d))
    Cb_halfEdisc = 0.5 * Edisc
    return dict(n=n, m=m, l2=l2, H=H, C=C, absC=abs(C), Rpp=Rpp,
                Cb_cs=Cb_cs, Cb_hub=hub, Cb_w1=Cb_w1, Cb_wmin=Cb_wmin,
                Cb_whub=Cb_whub, Cb_pv=Cb_pv, Cb_halfEdisc=Cb_halfEdisc,
                contrib=contrib, d=d, fDf=fDf)


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
    rows = [analyse(G) for G in corpus(9)]
    rows = [r for r in rows if r["l2"] > 1e-6]
    hard = [r for r in rows if r["C"] < -1e-9 and r["Cb_cs"] > r["Rpp"] + 1e-9]
    print(f"corpus {len(rows)};  HARD CORE (C<0 & Cb_cs>R''): {len(hard)}")
    Hh = np.array([r["H"] for r in hard])
    print(f"  H on hard core: min={Hh.min():.3f} median={np.median(Hh):.3f} max={Hh.max():.3f}")

    # ===== TASK 1: anatomy =====
    print("\n===== TASK 1: anatomy of C on hard core =====")
    # dominant edges: fraction of |C| from edges with d_l = min-degree; (d_h-d_l) dist; f_h vs f_l
    frac_minl = []; dd_dom = []; fh_small = []; sign_fh_term = []
    for r in hard:
        dmin = r["d"].min()
        terms = sorted(r["contrib"], key=lambda t: -abs(t[0]))
        top = terms[:max(1, len(terms) // 5)]            # top 20% edges by |contrib|
        tot = sum(abs(t[0]) for t in r["contrib"]) + 1e-12
        frac_minl.append(sum(abs(t[0]) for t in top if t[2] == dmin) / tot)
        for t in top:
            dd_dom.append(t[5])
            fh_small.append(abs(t[3]) < abs(t[4]))       # is f_h smaller than f_l? (hub-flat)
            sign_fh_term.append(np.sign(t[3] * (t[3] - t[4])))  # sign of f_h(f_h-f_l)
    print(f"  frac of |C| (top-20% edges) on edges touching MIN-degree vertex: "
          f"median={np.median(frac_minl):.3f}")
    print(f"  degree gap (d_h-d_l) on dominant edges: median={np.median(dd_dom):.1f} "
          f"max={int(np.max(dd_dom))}")
    print(f"  on dominant edges |f_h|<|f_l| (hub flat, leaf large): {100*np.mean(fh_small):.0f}%")
    print(f"  sign of f_h(f_h-f_l) on dominant edges: "
          f"<0 (drives C negative): {100*np.mean(np.array(sign_fh_term)<0):.0f}%")

    # ===== TASK 2/3: test each bound =====
    print("\n===== TASK 2/3: bound/R'' on hard core (want max ≤ 1) =====")
    names = [("(orig) Cb_cs", "Cb_cs"), ("(a) hub-flat", "Cb_hub"),
             ("(b) ½E_disc", "Cb_halfEdisc"), ("(c) w=Δd", "Cb_w1"),
             ("(c) w=d_l-1", "Cb_wmin"), ("(c) w=1/(d_h-λ)²", "Cb_whub"),
             ("(d) per-vertex", "Cb_pv")]
    for label, key in names:
        B = np.array([r[key] for r in hard])
        Rp = np.array([r["Rpp"] for r in hard])
        absC = np.array([r["absC"] for r in hard])
        valid = int(np.sum(B >= absC - 1e-7))            # is it a valid upper bound on |C|?
        ratio = B / np.maximum(Rp, 1e-12)
        cov = int(np.sum(B <= Rp + 1e-9))
        print(f"  {label:18s}: valid(|C|≤B) {valid}/{len(hard)} | "
              f"B/R'' median={np.median(ratio):6.3f} max={ratio.max():7.3f} | "
              f"covers(B≤R'') {cov}/{len(hard)} ({100*cov/len(hard):.1f}%)")

    # ===== TASK 4: combine / min over valid bounds =====
    print("\n===== TASK 4: combine bounds =====")
    valid_keys = ["Cb_cs", "Cb_hub", "Cb_w1", "Cb_wmin", "Cb_whub", "Cb_pv", "Cb_halfEdisc"]
    # per-graph MIN over bounds that are valid (>= |C|)
    minB = []; Rp = []
    for r in hard:
        bs = [r[k] for k in valid_keys if r[k] >= r["absC"] - 1e-7]
        minB.append(min(bs) if bs else min(r[k] for k in valid_keys))
        Rp.append(r["Rpp"])
    minB = np.array(minB); Rp = np.array(Rp)
    cov = int(np.sum(minB <= Rp + 1e-9))
    print(f"  MIN over valid bounds ≤ R'': {cov}/{len(hard)} ({100*cov/len(hard):.1f}%) "
          f"| max ratio={np.max(minB/np.maximum(Rp,1e-12)):.3f}")
    # ===== FULL-CORPUS test: does any single bound give |C| ≤ bound ≤ R'' EVERYWHERE? =====
    # (that would prove C+R'' ≥ 0 on all graphs, since |C| ≤ bound ≤ R'' ⟹ C ≥ -R'')
    print("\n===== FULL-CORPUS: bound ≤ R'' on ALL graphs? (excl. K_n where R''=0) =====")
    full = [r for r in rows if r["Rpp"] > 1e-9]          # drop K_n (R''=0, C=0)
    nKn = len(rows) - len(full)
    for label, key in names:
        ratios = np.array([r[key] / r["Rpp"] for r in full])
        valid = all(r[key] >= r["absC"] - 1e-7 for r in full)
        cov = int(np.sum(ratios <= 1 + 1e-9))
        flag = "  *** CLOSES B2' ***" if ratios.max() <= 1 + 1e-6 else ""
        print(f"  {label:18s}: valid={valid} | max B/R''={ratios.max():7.3f} | "
              f"covers {cov}/{len(full)} ({100*cov/len(full):.2f}%){flag}")
    print(f"  (excluded {nKn} graphs with R''=0; there C=0 so C+R''=0 trivially)")


if __name__ == "__main__":
    main()
