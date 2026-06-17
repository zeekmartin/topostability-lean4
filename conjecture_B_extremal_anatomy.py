"""
Three experiments on deg2+dense (the binding family).
C+R'' = fᵀKf with K = Q_C + λ₂(A + I - ddᵀ/m), where Q_C is the oriented-C quadratic
form: Q_C[h,h]+=(d_h-d_l), Q_C[h,l]=Q_C[l,h]-=(d_h-d_l)/2 for each edge (h=higher deg).

TASK A: decompose f in K's eigenbasis -> pos_part, neg_part (cancellation vs avoidance).
TASK B: convergence rate of margin 1-|C|/R'' vs n (power/log/exp fit).
TASK C: aggregation-loss anatomy of the per-vertex bound (sign cancellation among C(l)?).
Run:  python conjecture_B_extremal_anatomy.py
"""
import numpy as np
import networkx as nx


def build(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    QC = np.zeros((n, n)); Cl = np.zeros(n)
    for i, j in np.argwhere(np.triu(A, 1) > 0.5):
        if d[i] == d[j]:
            continue
        h, lo = (i, j) if d[i] > d[j] else (j, i)
        g = d[h] - d[lo]
        QC[h, h] += g
        QC[h, lo] -= g / 2; QC[lo, h] -= g / 2
        Cl[lo] += g * f[h] * (f[h] - f[lo])
    C = float(f @ QC @ f)
    K = QC + l2 * (A + np.eye(n) - np.outer(d, d) / m)
    return dict(n=n, m=m, l2=l2, f=f, d=d, A=A, K=K, C=C, Rpp=Rpp, Cl=Cl, fDf=fDf)


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def taskA():
    print("===== TASK A: f in K's eigenbasis (K: fᵀKf = C+R'') =====")
    print("   n  | C+R''   | pos_part | neg_part | neg/pos | (cancellation? avoidance?)")
    for n in (50, 100, 200, 500):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        r = build(G)
        w, U = np.linalg.eigh(r["K"])
        a = U.T @ r["f"]                       # coords of f
        pos = float(np.sum(w[w > 0] * a[w > 0] ** 2))
        neg = float(np.sum(-w[w < 0] * a[w < 0] ** 2))
        fKf = pos - neg
        ratio = neg / pos if pos > 0 else float("nan")
        mode = "CANCELLATION" if ratio > 0.5 else ("avoidance" if ratio < 0.05 else "mixed")
        print(f"  {n:4d} | {fKf:7.3f} | {pos:8.2f} | {neg:8.2f} | {ratio:6.3f}  | {mode}")
    print("  (corpus-wide M=λ₂Q-L_t had ~600× avoidance gap; here K is the C+R'' operator)")


def taskB():
    print("\n===== TASK B: convergence of margin 1-|C|/R'' vs n =====")
    ns = [30, 50, 100, 200, 350, 500, 750, 1000, 1500]
    data = []
    for n in ns:
        ms = []; crs = []; rps = []
        for s in range(6 if n <= 200 else 3):
            G = deg2dense(n, 0.65, seed=900 + n + 7 * s)
            if not nx.is_connected(G):
                continue
            r = build(G)
            if r["Rpp"] > 1e-9:
                ms.append(1 - abs(r["C"]) / r["Rpp"])
                crs.append(r["C"] + r["Rpp"]); rps.append(r["Rpp"])
        if ms:
            data.append((n, np.mean(ms), np.mean(crs), np.mean(rps)))
            print(f"  n={n:5d}: margin(1-|C|/R'')={np.mean(ms):.4f}  C+R''={np.mean(crs):.3f}  "
                  f"R''={np.mean(rps):.3f}")
    arr = np.array(data)
    nn = arr[:, 0]; mg = arr[:, 1]
    # power law: log mg = log a - β log n
    bp, ap = np.polyfit(np.log(nn), np.log(mg), 1)
    pred_p = np.exp(ap) * nn ** bp
    r2p = 1 - np.sum((mg - pred_p) ** 2) / np.sum((mg - mg.mean()) ** 2)
    # log: mg = a / log n
    al = np.sum(mg * (1 / np.log(nn))) / np.sum((1 / np.log(nn)) ** 2)
    pred_l = al / np.log(nn)
    r2l = 1 - np.sum((mg - pred_l) ** 2) / np.sum((mg - mg.mean()) ** 2)
    # exp: log mg = log a - b n
    be, ae = np.polyfit(nn, np.log(mg), 1)
    pred_e = np.exp(ae) * np.exp(be * nn)
    r2e = 1 - np.sum((mg - pred_e) ** 2) / np.sum((mg - mg.mean()) ** 2)
    print(f"  FITS:  power a·n^(-β): β={-bp:.3f} R²={r2p:.4f} | "
          f"log a/log n: R²={r2l:.4f} | exp a·e^(-bn): R²={r2e:.4f}")
    best = max([("power", r2p), ("log", r2l), ("exp", r2e)], key=lambda t: t[1])
    print(f"  best fit: {best[0]} (R²={best[1]:.4f})  "
          f"=> margin {'→0 polynomially' if best[0]=='power' else best[0]}")


def taskC():
    print("\n===== TASK C: aggregation-loss anatomy of  -C(l) ≤ λ₂ d_l f_l² =====")
    for n in (100, 200, 500):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        r = build(G); Cl = r["Cl"]; d = r["d"]; f = r["f"]; l2 = r["l2"]
        pos = Cl > 1e-12; neg = Cl < -1e-12
        absC = abs(Cl.sum())
        sumAbs = float(np.sum(np.abs(Cl)))
        bound = float(np.sum(l2 * d * f * f))           # full Σ λ₂ d_l f_l²
        bound_neg = float(np.sum(l2 * d[neg] * f[neg] ** 2))
        # loss decomposition: bound_neg / |C|  =  (bound_neg/Σ_{neg}|C(l)|)·(Σ_{neg}|C(l)|/|C|)
        sum_negC = float(np.sum(-Cl[neg]))
        per_vertex_loose = bound_neg / sum_negC if sum_negC > 0 else float("nan")
        sign_cancel = sum_negC / absC if absC > 0 else float("nan")
        print(f"  n={n}: #C(l)>0={int(pos.sum())} #C(l)<0={int(neg.sum())} "
              f"(of {int((d>0).sum())} verts)")
        print(f"     Σ|C(l)|={sumAbs:.3f}  |C|=|ΣC(l)|={absC:.3f}  ratio Σ|C(l)|/|C|={sumAbs/absC:.2f} "
              f"(>1 ⇒ sign cancellation)")
        print(f"     loss split: λ₂M_neg/|C|={bound_neg/absC:.2f} = "
              f"[per-vertex loose {per_vertex_loose:.2f}] × [neg-only/|C| {sign_cancel:.2f}]")
        # structural split: do C(l)>0 vs <0 separate by degree of l?
        if pos.sum() and neg.sum():
            print(f"     degree of l:  C(l)>0 mean d_l={d[pos].mean():.1f}  "
                  f"C(l)<0 mean d_l={d[neg].mean():.1f}  (min deg={int(d.min())})")
        # where is C concentrated?
        order = np.argsort(Cl)
        print(f"     most-negative C(l): vertex deg={int(d[order[0]]):d}, C(l)={Cl[order[0]]:.3f} "
              f"(min-degree vertex carries the negativity: {d[order[0]]==d.min()})")


if __name__ == "__main__":
    taskA()
    taskB()
    taskC()
