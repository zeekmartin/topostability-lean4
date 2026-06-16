"""
Conjecture B proof v2 — formalising the S2 (Fiedler-lift projection) witness.

Reduction (established):  lambda2(T(G)) <= lambda2(G)  holds if
    mu(G) := min_{phi ⟂ d}  (phi^T L_t phi)/(phi^T Q phi)   <=  lambda2(G),
with L_t the triangle-weighted Laplacian and Q = D + A the signless Laplacian.

S2 witness (edge-space projection of the RAW Fiedler f, L_G f = lambda2 f, f⟂1):
    h  = B^T f                  (unsigned lift,  h_e = f_u + f_v)
    h' = h - (S/m) 1_E ⟂ 1_E    (S = f·d = sum_v deg(v) f(v),  m = |E|)
  Since L_{T(G)} 1_E = 0, the numerator is UNCHANGED, so
    R_{T(G)}(h') = (f^T L_t f) / (f^T Q f - S^2/m),
  and the target inequality is        f^T L_t f  <=  lambda2 (f^T Q f - S^2/m).

This script:
  (A) verifies the operator identities  L_t = B L_{T(G)} B^T,  Q = B B^T;
  (B) tests the near-optimality structural claim: mu(G) is a Rayleigh-Ritz value
      of L_{T(G)} on the additive subspace U = range(B^T); mu = lambda2(T) iff the
      T(G)-Fiedler is additive. Measures the additive overlap ||P_U psi_T||;
  (C) tests the S2 target and a battery of PROVABLE upper bounds on f^T L_t f
      (t_ab <= Delta-1; <= min(da,db)-1; <= (da+db)/2-1) to see which, if any,
      closes  upper-bound <= lambda2 (f^T Q f - S^2/m);
  (D) evaluates the explicit degree-sum identity (derived by hand) for the
      (da+db)/2 weighted form using L_G f = lambda2 f.

Run:  python conjecture_B_proof_v2_explore.py
"""
import os
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9
HERE = os.path.dirname(os.path.abspath(__file__))


def ops(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    B = np.zeros((n, m))
    for e, (u, v) in enumerate(edges):
        B[idx[u], e] = 1.0; B[idx[v], e] = 1.0
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    D = np.diag(L.diagonal()); A = D - L; Q = D + A
    deg = L.diagonal().copy()
    # triangle-weighted, min-deg-weighted, deg-sum-weighted Laplacians
    W_t = np.zeros((n, n)); W_md = np.zeros((n, n)); W_ds = np.zeros((n, n))
    for u, v in edges:
        i, j = idx[u], idx[v]
        t = len(set(G[u]) & set(G[v]))
        W_t[i, j] = W_t[j, i] = t
        W_md[i, j] = W_md[j, i] = min(deg[i], deg[j]) - 1
        W_ds[i, j] = W_ds[j, i] = (deg[i] + deg[j]) / 2.0 - 1.0
    Lt = np.diag(W_t.sum(1)) - W_t
    Lmd = np.diag(W_md.sum(1)) - W_md
    Lds = np.diag(W_ds.sum(1)) - W_ds
    T = ce.triangle_graph(G)
    Tconn = T.number_of_nodes() >= 2 and nx.is_connected(T)
    LT = nx.laplacian_matrix(T).toarray().astype(float) if Tconn else None
    evL, vL = np.linalg.eigh(L); l2G = float(evL[1]); f = vL[:, 1].copy()
    return dict(nodes=nodes, edges=edges, n=n, m=m, B=B, L=L, D=D, A=A, Q=Q,
                Lt=Lt, Lmd=Lmd, Lds=Lds, T=T, Tconn=Tconn, LT=LT,
                l2G=l2G, f=f, deg=deg,
                l2T=(ce.lambda2(T) if Tconn else None))


def sym_geneig(M, S):
    Lc = np.linalg.cholesky(S)
    Y = np.linalg.solve(Lc, np.linalg.solve(Lc, M).T).T
    return np.linalg.eigvalsh(0.5 * (Y + Y.T))


def mu_on_dperp(Lt, Q, deg):
    c = deg / np.linalg.norm(deg)
    _, _, Vt = np.linalg.svd(np.outer(c, c)); P = Vt[1:].T
    w = sym_geneig(P.T @ Lt @ P, P.T @ Q @ P)
    return float(np.min(w))


def analyse(G):
    o = ops(G)
    if not o["Tconn"] or o["l2T"] is None or o["l2T"] <= TOL:
        return None
    B, L, Q, Lt, LT = o["B"], o["L"], o["Q"], o["Lt"], o["LT"]
    Lmd, Lds = o["Lmd"], o["Lds"]
    l2G, l2T, f, deg = o["l2G"], o["l2T"], o["f"], o["deg"]
    n, m = o["n"], o["m"]
    Delta = int(deg.max()); delta = int(deg.min())

    # (A) operator identities
    id_Lt = float(np.max(np.abs(B @ LT @ B.T - Lt)))
    id_Q = float(np.max(np.abs(B @ B.T - Q)))

    # (B) Rayleigh-Ritz near-optimality
    Q_pd = np.linalg.eigvalsh(Q)[0] > 1e-9
    mu = mu_on_dperp(Lt, Q, deg) if Q_pd else None
    # additive subspace projector P_U = B^T (B B^T)^-1 B  (onto range(B^T) in R^E)
    BBt = B @ B.T
    P_U = B.T @ np.linalg.solve(BBt, B)
    evT, vT = np.linalg.eigh(LT)
    psiT = vT[:, 1].copy()                       # T(G)-Fiedler (unit)
    overlap = float(np.linalg.norm(P_U @ psiT))  # 1 == fully additive
    ritz_gap = (mu - l2T) if mu is not None else float("nan")

    # (C) S2 target and provable upper bounds
    S = float(deg @ f)
    fQf = float(f @ Q @ f)
    den = fQf - S * S / m
    T1 = float(f @ Lt @ f)                       # exact numerator
    target_rhs = l2G * den                       # exact S2 RHS
    s2 = T1 <= target_rhs + 1e-7
    # provable upper bounds on T1 (weight >= t_ab edgewise):
    U_delta = (Delta - 1) * l2G                  # crude (t<=Delta-1, f^T L_G f=l2G)
    U_md = float(f @ Lmd @ f)                    # t <= min(da,db)-1
    U_ds = float(f @ Lds @ f)                    # t <= (da+db)/2-1
    closes_delta = U_delta <= target_rhs + 1e-7
    closes_md = U_md <= target_rhs + 1e-7
    closes_ds = U_ds <= target_rhs + 1e-7
    # sanity: each U must dominate T1
    dom = (T1 <= U_md + 1e-7) and (T1 <= U_ds + 1e-7) and (T1 <= U_delta + 1e-7)

    # (D) degree-sum identity check:
    #   sum_{ab}(da+db)(f_a-f_b)^2 = 2 l2 sum_v deg_v f_v^2 + sum_v f_v^2 disc(v)
    #   disc(v) = sum_{b~v}(deg_b - deg_v)
    A = o["A"]
    disc = (A @ deg) - deg * deg                 # (A deg)_v - deg_v^2 = sum_{b~v}(deg_b-deg_v)
    sum_ds_full = float(f @ (2 * Lds + 2 * L) @ f)  # = sum(da+db)(.)^2 since Lds uses (da+db)/2-1; +L adds back the -1
    # rebuild raw sum_{ab}(da+db)(dphi)^2 directly:
    raw = 0.0
    for u, v in o["edges"]:
        i = o["nodes"].index(u); j = o["nodes"].index(v)
        raw += (deg[i] + deg[j]) * (f[i] - f[j]) ** 2
    fDf = float((deg * f * f).sum())
    ident_rhs = 2 * l2G * fDf + float((f * f) @ disc)
    id_degsum = abs(raw - ident_rhs) < 1e-6

    return dict(name=None, n=n, m=m, Delta=Delta, delta=delta,
                l2G=l2G, l2T=l2T, Q=l2G / l2T, mu=mu, ritz_gap=ritz_gap,
                overlap=overlap, id_Lt=id_Lt, id_Q=id_Q, id_degsum=id_degsum,
                S=S, T1=T1, target_rhs=target_rhs, den=den, s2=s2,
                U_delta=U_delta, U_md=U_md, U_ds=U_ds,
                closes_delta=closes_delta, closes_md=closes_md,
                closes_ds=closes_ds, dom=dom, fDf=fDf,
                regular=(Delta == delta))


def test_graphs():
    out = []

    def add(name, G):
        if G.number_of_nodes() >= 3 and nx.is_connected(G):
            out.append((name, G))

    for n in range(6, 11):
        K = nx.complete_graph(n); edges = list(K.edges())
        for k in (1, 2, 3):
            G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges[k:])
            add(f"K{n}-minus{k}e", G)
        G = nx.complete_graph(n)
        for j in range(2, n):
            G.remove_edge(0, j)
        add(f"K{n}-star0", G)
    for parts in ([4, 3], [5, 3], [4, 4, 1], [5, 2, 2], [3, 3, 2], [6, 3],
                  [4, 3, 2], [5, 4]):
        add(f"Kmulti{parts}", nx.complete_multipartite_graph(*parts))
    for n in (7, 8, 9):
        G = nx.complete_graph(n - 1); G.add_edge(n - 1, 0); add(f"K{n-1}+pendant", G)
        G2 = nx.complete_graph(n - 1); G2.add_edges_from([(n - 1, 0), (n - 1, 1)])
        add(f"K{n-1}+deg2", G2)
    rng = np.random.default_rng(7); seen = set(); cand = []
    for _ in range(4000):
        n = int(rng.integers(7, 11)); p = float(rng.uniform(0.6, 0.95))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G) or ce.is_regular(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        l2T = ce.lambda2(T)
        if l2T <= TOL:
            continue
        Qv = ce.lambda2(G) / l2T
        key = (n, G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key in seen:
            continue
        seen.add(key); cand.append((Qv, G))
    cand.sort(key=lambda x: x[0])
    for i, (Qv, G) in enumerate(cand[:30]):
        add(f"rand-tight{i}-Q{Qv:.3f}", G)
    return out


def main():
    print("building test set...")
    rows = []
    for name, G in test_graphs():
        r = analyse(G)
        if r is None:
            continue
        r["name"] = name
        rows.append(r)
    irr = sorted((r for r in rows if not r["regular"]), key=lambda r: r["Q"])
    N = len(rows)
    print(f"  {N} analysed ({len(irr)} irregular)")

    ids_Lt = max(r["id_Lt"] for r in rows)
    ids_Q = max(r["id_Q"] for r in rows)
    ids_ds = all(r["id_degsum"] for r in rows)
    n_s2 = sum(1 for r in rows if r["s2"])
    n_cd = sum(1 for r in rows if r["closes_delta"])
    n_cmd = sum(1 for r in rows if r["closes_md"])
    n_cds = sum(1 for r in rows if r["closes_ds"])
    n_dom = sum(1 for r in rows if r["dom"])
    min_overlap = min(r["overlap"] for r in rows)
    max_ritzgap = max(r["ritz_gap"] for r in rows if r["mu"] is not None)

    print("\n=== v2 verdicts (%d graphs) ===" % N)
    print(f"(A) operator identities: max|B L_T B^T - L_t|={ids_Lt:.2e}  "
          f"max|B B^T - Q|={ids_Q:.2e}")
    print(f"(B) near-opt: min additive overlap ||P_U psi_T|| = {min_overlap:.4f}  "
          f"(1=fully additive); max Ritz gap mu-l2T = {max_ritzgap:.4f}")
    print(f"(C) S2 target  f^T L_t f <= l2G(f^TQf - S^2/m): {n_s2}/{N}")
    print(f"    closes via t<=Delta-1       : {n_cd}/{N}")
    print(f"    closes via t<=min(da,db)-1  : {n_cmd}/{N}")
    print(f"    closes via t<=(da+db)/2-1   : {n_cds}/{N}")
    print(f"    (sanity) upper bounds dominate T1: {n_dom}/{N}")
    print(f"(D) degree-sum identity holds: {ids_ds}")
    print("\ntightest 12 irregular (overlap, Ritz gap, which bounds close):")
    print("  name                         Q     overlap muGap  s2 md ds")
    for r in irr[:12]:
        print(f"  {r['name']:28s} {r['Q']:.3f} {r['overlap']:.4f} "
              f"{r['ritz_gap']:+.3f}  "
              f"{'Y' if r['s2'] else 'N':>2s} {'Y' if r['closes_md'] else 'N':>2s} "
              f"{'Y' if r['closes_ds'] else 'N':>2s}")

    main.rows = rows; main.irr = irr
    main.summary = dict(N=N, ids_Lt=ids_Lt, ids_Q=ids_Q, ids_ds=ids_ds,
                        n_s2=n_s2, n_cd=n_cd, n_cmd=n_cmd, n_cds=n_cds,
                        min_overlap=min_overlap, max_ritzgap=max_ritzgap)


if __name__ == "__main__":
    main()
