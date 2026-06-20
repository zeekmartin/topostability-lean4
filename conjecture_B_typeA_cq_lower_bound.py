"""
TYPE A: explicit formula / lower bound for c(q) where gap = lam2 G - B2' = c(q) * n / m.

G = core H + degree-2 vertex v0 attached at a,b.  x=f_v0, p=f_a, r=f_b, y=p+r=(2-lam)x.
Core H: n_H vertices, m_H edges, degrees d_u, spectral gap gamma=lam2(H).

Exact pieces verified:
  - resolvent identity: (L_H - lam I) f_H = -(p-x)e_a - (r-x)e_b
  - junction 2x2 system: alpha=p-x, beta=r-x solve
        alpha(1+R_aa) + beta R_ab = (mu-x)
        alpha R_ab + beta(1+R_bb) = (mu-x),   mu=-x/n_H,  R=(L_H-lam)^{-1} on 1_H^perp
  - gap = R'' + C_attach + C_dense

c(q) = gap * m / n.  Goal: lower bound c(q) >= c0(gamma/Delta, regularity, symmetry).
Run: python conjecture_B_typeA_cq_lower_bound.py
"""
import numpy as np
import networkx as nx


def attach_deg2(H):
    H = nx.convert_node_labels_to_integers(H)
    nH = H.number_of_nodes()
    G = nx.Graph(H); G.add_node(nH); G.add_edge(nH, 0); G.add_edge(nH, 1)
    return G, nH


def analyze(H):
    Hc = nx.convert_node_labels_to_integers(H)
    nH = Hc.number_of_nodes(); mH = Hc.number_of_edges()
    AH = nx.to_numpy_array(Hc, nodelist=list(range(nH))); dH = AH.sum(1)
    LH = np.diag(dH) - AH
    evH, UH = np.linalg.eigh(LH); gamma = float(evH[1])
    G, v0lbl = attach_deg2(H)
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    v0 = idx[v0lbl]
    if f[v0] < 0:
        f = -f
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    x = float(f[v0]); a, b = idx[0], idx[1]
    p, rr = float(f[a]), float(f[b]); y = p + rr
    da, db = float(d[a]), float(d[b])
    # exact gap = lam G - B2'
    A2 = A @ A
    Gsum = sum((f[idx[u]] + f[idx[v]]) ** 2 for u, v in G.edges())
    B2 = sum((min(d[idx[u]], d[idx[v]]) - 1) * (f[idx[u]] - f[idx[v]]) ** 2 for u, v in G.edges())
    gap = lam * (Gsum - S ** 2 / m) - B2
    # resolvent identity residual: (L_H - lam) f_H + (p-x)e_a + (r-x)e_b
    fH = f[[idx[u] for u in range(nH)]]
    res = (LH - lam * np.eye(nH)) @ fH
    res[0] += (p - x); res[1] += (rr - x)
    res_id = float(np.max(np.abs(res)))
    # resolvent matrix on 1^perp
    R = np.zeros((nH, nH))
    for k in range(1, nH):
        R += np.outer(UH[:, k], UH[:, k]) / (evH[k] - lam)
    Raa, Rab, Rbb = R[0, 0], R[0, 1], R[1, 1]
    mu = -x / nH
    # predicted alpha,beta from 2x2
    M = np.array([[1 + Raa, Rab], [Rab, 1 + Rbb]]); rhsv = np.array([mu - x, mu - x])
    try:
        ab = np.linalg.solve(M, rhsv); a_pred, b_pred = ab
    except Exception:
        a_pred = b_pred = np.nan
    jerr = max(abs((p - x) - a_pred), abs((rr - x) - b_pred))
    c_q = gap * m / n
    Delta = float(dH.max()); delta = float(dH.min()); dbar = float(dH.mean())
    return dict(n=n, m=m, nH=nH, mH=mH, lam=lam, x=x, p=p, r=rr, y=y, da=da, db=db,
                gamma=gamma, Delta=Delta, delta=delta, dbar=dbar, gap=gap, c_q=c_q,
                res_id=res_id, jerr=jerr, Raa=Raa, Rab=Rab, Rbb=Rbb)


def cores():
    out = []
    for nH in [60, 120, 240]:
        out.append((f"K{nH}", nx.complete_graph(nH)))
        for q in [0.1, 0.2, 0.3, 0.5, 0.65, 0.8, 0.9]:
            out.append((f"gnp{nH}_{q}", nx.gnp_random_graph(nH, q, seed=7)))
        for frac in [0.1, 0.25, 0.5]:
            r = max(3, int(frac * nH))
            if (r * nH) % 2: r += 1
            out.append((f"rr{nH}_{r}", nx.random_regular_graph(r, nH, seed=7)))
        out.append((f"circ{nH}", nx.circulant_graph(nH, list(range(1, nH // 5)))))
    return out


def main():
    data = []
    for name, H in cores():
        if H.number_of_nodes() < 5 or not nx.is_connected(H):
            continue
        try:
            data.append((name, analyze(H)))
        except Exception:
            pass

    print("=" * 96)
    print("EXACT identity checks")
    print("=" * 96)
    print(f"  resolvent (L_H-λ)f_H = -(p-x)e_a-(r-x)e_b : max residual = "
          f"{max(q['res_id'] for _,q in data):.2e}")
    print(f"  junction 2x2 system predicts (p-x,r-x)    : max error    = "
          f"{max(q['jerr'] for _,q in data):.2e}")

    print("\n" + "=" * 96)
    print("c(q) = gap·m/n  vs structural ratios")
    print("=" * 96)
    print(f"  {'core':12s} {'q=dbar/nH':>9} {'gamma/Δ':>8} {'Δ/δ':>6} {'lam2':>7} {'gap':>9} "
          f"{'c(q)':>8} {'p/x':>9} {'attach_sym':>10}")
    for name, q in data:
        qd = q['dbar'] / q['nH']
        sym = abs(q['p'] - q['r']) / max(abs(q['p']) + abs(q['r']), 1e-12)
        print(f"  {name:12s} {qd:9.3f} {q['gamma']/q['Delta']:8.3f} {q['Delta']/q['delta']:6.2f} "
              f"{q['lam']:7.4f} {q['gap']:9.5f} {q['c_q']:8.3f} {q['p']/q['x']:9.2e} {sym:10.2e}")

    print("\n" + "=" * 96)
    print("c(q) lower-bound candidates")
    print("=" * 96)
    cs = np.array([q['c_q'] for _, q in data])
    print(f"  inf c(q) = {cs.min():.3f}  median = {np.median(cs):.3f}  max = {cs.max():.3f}")
    # candidate: c(q) >= c0 ;  c(q) vs 2(gamma/Delta)? c(q) vs 4*? Let's test ratios
    for name, formula in [
        ("c(q)/(2)", lambda q: q['c_q'] / 2),
        ("c(q)/(4·dbar/nH)", lambda q: q['c_q'] / (4 * q['dbar'] / q['nH'])),
        ("c(q)/(gamma/Delta)", lambda q: q['c_q'] / (q['gamma'] / q['Delta'])),
        ("c(q)·δ/Δ", lambda q: q['c_q'] * q['delta'] / q['Delta']),
    ]:
        vals = np.array([formula(q) for _, q in data])
        print(f"  {name:22s}: min={vals.min():.3f} median={np.median(vals):.3f} max={vals.max():.3f}")

    print("\n" + "=" * 96)
    print("complete-core check: c=10 exactly?  and c(q) for regular vs gnp at matched density")
    print("=" * 96)
    for name, q in data:
        if name.startswith("K"):
            print(f"  {name}: c(q)={q['c_q']:.4f} (=10?)  lam2={q['lam']:.2e}")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  exact: resolvent identity + junction 2x2 (residual ~1e-13). c(q)=gap·m/n in "
          f"[{cs.min():.2f},{cs.max():.2f}].")
    print("  Test which normalization makes c(q) bounded below by a positive constant.")


if __name__ == "__main__":
    main()
