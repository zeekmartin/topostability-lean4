"""
Course correction: target the ACTUAL-triangle operator M = λ₂Q - L_t (not the min-degree
relaxation K). Q = D+A; L_t = triangle-weighted Laplacian, edge weight t_ab=(A²)_ab.

TASK 1: margin_B = 1-λ₂(T(G))/λ₂(G) (real) vs margin_B2=(C+R'')/R'' vs margin_M.
TASK 2: f in M's eigenbasis -> neg/pos avoidance at scale (vs K's 0.996 cancellation).
TASK 3: per-edge gap (min(d_a,d_b)-1) - t_ab : concentrated on the degree-2 vertex?
TASK 4: (a) #neg eigvals of M|1⊥; (b) L_t≼λ₂Q real vs min; (c) hub-flat + real t_ab.
Run:  python conjecture_B_real_triangles.py
"""
import numpy as np
import networkx as nx
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import eigsh


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def vertex_quant(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    W = A * A2                                   # W_ab = t_ab on edges
    Lt = np.diag(W @ np.ones(n)) - W
    Q = np.diag(d) + A
    M = l2 * Q - Lt
    fDf = float((d * f * f).sum()); S = float(d @ f)
    fQf = float(f @ Q @ f); fLtf = float(f @ Lt @ f)
    Rpp = l2 * (fDf - l2 + 1 - S * S / m)
    # C (min-deg oriented) and W1
    C = 0.0; W1 = 0.0
    for i, j in np.argwhere(np.triu(A, 1) > 0.5):
        if d[i] != d[j]:
            h, lo = (i, j) if d[i] > d[j] else (j, i)
            C += (d[h] - d[lo]) * f[h] * (f[h] - f[lo])
        W1 += (min(d[i], d[j]) - 1) * (f[i] - f[j]) ** 2
    fMf = float(f @ M @ f)
    return dict(n=n, m=m, l2=l2, f=f, d=d, A=A, A2=A2, Q=Q, Lt=Lt, M=M, idx=idx,
                fDf=fDf, S=S, fQf=fQf, fLtf=fLtf, Rpp=Rpp, C=C, W1=W1, fMf=fMf, nodes=nodes)


def lambda2_TG(G, maxv=30000):
    """λ₂ of the triangle graph T(G), built directly; sparse shift-invert."""
    nodes = list(G.nodes())
    eidx = {}
    for e in G.edges():
        eidx[frozenset(e)] = len(eidx)
    ne = len(eidx)
    if ne > maxv:
        return None
    rows = []; cols = []
    adj = {v: list(G.neighbors(v)) for v in nodes}
    seen = set()
    for v in nodes:
        Nv = adj[v]
        for a in range(len(Nv)):
            for b in range(a + 1, len(Nv)):
                u, w = Nv[a], Nv[b]
                if G.has_edge(u, w):                 # triangle v-u-w
                    e1 = eidx[frozenset((v, u))]; e2 = eidx[frozenset((v, w))]
                    key = (min(e1, e2), max(e1, e2))
                    if key not in seen:
                        seen.add(key)
                        rows.append(e1); cols.append(e2)
                        rows.append(e2); cols.append(e1)
    if not rows:
        return None
    Aadj = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(ne, ne))
    deg = np.array(Aadj.sum(axis=1)).flatten()
    Ldeg = csr_matrix((deg, (range(ne), range(ne))), shape=(ne, ne))
    LT = (Ldeg - Aadj).astype(float)
    try:
        vals = eigsh(LT, k=2, sigma=1e-6, which='LM', return_eigenvectors=False, maxiter=5000)
        return float(sorted(vals)[1])
    except Exception:
        return None


def main():
    print("===== TASK 1: real margin_B vs relaxation margin_B2 vs margin_M =====")
    print("   n  | λ₂(G) | λ₂(T) | margin_B=1-λ₂T/λ₂G | margin_B2 | margin_M")
    margB = []
    for n in (50, 100, 150, 200):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        r = vertex_quant(G)
        l2T = lambda2_TG(G)
        mB = 1 - l2T / r["l2"] if l2T else float("nan")
        if l2T:
            margB.append(mB)
        mB2 = (r["C"] + r["Rpp"]) / r["Rpp"]
        mM = r["fMf"] / (r["l2"] * r["fQf"])
        l2Ts = f"{l2T:.4f}" if l2T else "  -  "
        print(f"  {n:4d} | {r['l2']:.4f} | {l2Ts} | {mB:18.4f} | {mB2:9.4f} | {mM:8.4f}")
    # scale-only margins (margin_M, margin_B2) at large n
    print("  larger n (margin_M, margin_B2 only):")
    for n in (300, 500, 1000):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        r = vertex_quant(G)
        mB2 = (r["C"] + r["Rpp"]) / r["Rpp"]
        mM = r["fMf"] / (r["l2"] * r["fQf"])
        print(f"  {n:4d} | margin_B2={mB2:.4f}  margin_M={mM:.4f}")
    if margB:
        print(f"  => inf_n margin_B (real conjecture) on tested deg2+dense ≈ {min(margB):.4f}")

    print("\n===== TASK 2: f in M's eigenbasis (avoidance vs cancellation) =====")
    print("   n  | fᵀMf  | pos   | neg   | neg/pos | vs K(min-deg) neg/pos")
    for n in (100, 200, 500, 1000):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        r = vertex_quant(G)
        w, U = np.linalg.eigh(r["M"]); a = U.T @ r["f"]
        pos = float(np.sum(w[w > 1e-12] * a[w > 1e-12] ** 2))
        neg = float(np.sum(-w[w < -1e-12] * a[w < -1e-12] ** 2))
        ratio = neg / pos if pos > 0 else float("nan")
        print(f"  {n:4d} | {pos-neg:6.2f} | {pos:6.1f} | {neg:6.2f} | {ratio:.5f}  | (K≈0.996)")

    print("\n===== TASK 3: per-edge gap (min(d_a,d_b)-1) - t_ab =====")
    for n in (100, 200):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        r = vertex_quant(G); d = r["d"]; A2 = r["A2"]; A = r["A"]
        gaps_deg2 = []; gaps_other = []
        for i, j in np.argwhere(np.triu(A, 1) > 0.5):
            t = A2[i, j]; gap = (min(d[i], d[j]) - 1) - t
            if d[i] == 2 or d[j] == 2:
                gaps_deg2.append(gap)
            else:
                gaps_other.append(gap)
        gd = np.array(gaps_deg2); go = np.array(gaps_other)
        print(f"  n={n}: degree-2 vertex edges: gap mean={gd.mean():.2f} max={gd.max():.0f} (n={len(gd)})")
        print(f"        other edges:           gap mean={go.mean():.2f} max={go.max():.0f} (n={len(go)})")
        print(f"        => relaxation overestimates t by {gd.mean():.1f} on deg-2 edges "
              f"vs {go.mean():.1f} elsewhere")

    print("\n===== TASK 4: direct proof diagnostics for fᵀMf ≥ 0 =====")
    for n in (100, 200, 500):
        G = deg2dense(n, 0.65, seed=42 + n)
        if not nx.is_connected(G):
            continue
        r = vertex_quant(G); n_ = r["n"]
        ones = np.ones(n_); P = np.eye(n_) - np.outer(ones, ones) / n_
        # (a) #neg eigvals of M|1⊥
        wM = np.linalg.eigvalsh(P @ r["M"] @ P)
        # the ~0 eigenvalue along 1: drop the closest-to-structure; count strictly negative
        nneg_M = int(np.sum(wM < -1e-9))
        # K = λ₂Q - L_min  (min-deg weighted)  for comparison
        d = r["d"]; A = r["A"]
        Wmin = np.zeros((n_, n_))
        for i, j in np.argwhere(np.triu(A, 1) > 0.5):
            wt = min(d[i], d[j]) - 1
            Wmin[i, j] = wt; Wmin[j, i] = wt
        Lmin = np.diag(Wmin @ ones) - Wmin
        K = r["l2"] * r["Q"] - Lmin
        nneg_K = int(np.sum(np.linalg.eigvalsh(P @ K @ P) < -1e-9))
        # (b) operator margin: smallest eigenvalue of M|1⊥ (real) vs K|1⊥ (min)
        print(f"  n={n}: #neg eig M|1⊥={nneg_M}/{n_-1}  #neg eig K(min)|1⊥={nneg_K}/{n_-1}  "
              f"(fewer neg = closer to PSD)")
        # (c) hub-flat + real triangles: fᵀL_tf vs bound Σ t_ab(f_a-f_b)²; compare to λ₂(fQf-S²/m)
        lift_rhs = r["l2"] * (r["fQf"] - r["S"] ** 2 / r["m"])
        print(f"        fᵀL_tf={r['fLtf']:.3f}  W1(min)={r['W1']:.3f}  λ₂(fQf-S²/m)={lift_rhs:.3f}  "
              f"real-margin={1-r['fLtf']/lift_rhs:.3f} vs min-margin={1-r['W1']/lift_rhs:.3f}")


if __name__ == "__main__":
    main()
