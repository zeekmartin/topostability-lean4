"""
Proof exploration for Conjecture B:  lambda2(T(G)) <= lambda2(G).

Established reformulation (the genuine analytic core), derived and verified here:

  Lift the Fiedler vector. For phi in R^V define the edge vector h = B^T phi
  (UNSIGNED incidence B, |V|x|E|), i.e. h_e = phi_u + phi_v.  Then
      h^T L_{T(G)} h = sum_{(a,b) in E} t_ab (phi_a - phi_b)^2  =  phi^T L_t phi
      h^T h          = phi^T (D + A) phi                        =  phi^T Q phi
  where t_ab = |N(a) cap N(b)| (triangles through edge ab), L_t the
  triangle-WEIGHTED Laplacian, and Q = D + A the SIGNLESS Laplacian.
  h is a valid test vector for lambda2(T) iff h ⟂ 1_E  iff  phi ⟂ d (degree vec).

  Hence the lift route gives    lambda2(T) <= mu(G) := min_{phi ⟂ d} R(phi),
      R(phi) = (phi^T L_t phi) / (phi^T (D+A) phi),
  and Conjecture B follows (via this route) iff  mu(G) <= lambda2(G).

  NOTE the user's stated "core" ( (Bh)^T L_G (Bh) >= lambda2(T)|Bh|^2 for
  h ⟂ 1_E ) is the WRONG direction: for h ⟂ 1_E one has Bh ⟂ 1_V, so
  (Bh)^T L_G (Bh) >= lambda2(G)|Bh|^2 >= lambda2(T)|Bh|^2 automatically. Proving
  it yields nothing. The lift bound above is the correct sufficient condition.

This script tests three proof strategies numerically on the tightest irregular
graphs (where the regular-case proof breaks):

  S1  degree-weighted test vector  psi = phi/sqrt(deg)  (normalized-Laplacian framing)
  S2  Cauchy-Schwarz on the degree imbalance  S = sum_v deg(v) phi(v)
  S3  edge-space operator comparison of L_{T(G)} vs incidence operators

Run:  python conjecture_B_proof_explore.py
"""
import os
from itertools import combinations

import numpy as np
import networkx as nx

import counterexample_search as ce

TOL = 1e-9
HERE = os.path.dirname(os.path.abspath(__file__))


# --------------------------------------------------------------------------- #
# operators
# --------------------------------------------------------------------------- #
def operators(G):
    """Return dict of the matrices/quantities used throughout."""
    nodes = list(G.nodes())
    idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges())
    n, m = len(nodes), len(edges)

    B = np.zeros((n, m))                       # UNSIGNED incidence |V|x|E|
    for e, (u, v) in enumerate(edges):
        B[idx[u], e] = 1.0
        B[idx[v], e] = 1.0

    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    D = np.diag(L.diagonal())
    A = D - L
    Q = D + A                                  # signless Laplacian = B B^T

    # triangle-weighted Laplacian L_t (edge weight t_ab = #common nbrs)
    W = np.zeros((n, n))
    for u, v in edges:
        t = len(set(G[u]) & set(G[v]))
        W[idx[u], idx[v]] = t
        W[idx[v], idx[u]] = t
    Lt = np.diag(W.sum(1)) - W

    T = ce.triangle_graph(G)
    Tconn = T.number_of_nodes() >= 2 and nx.is_connected(T)
    LT = nx.laplacian_matrix(T).toarray().astype(float) if Tconn else None

    evL, evecL = np.linalg.eigh(L)
    l2G = float(evL[1])
    phi = evecL[:, 1].copy()                   # Fiedler vector of G
    deg = L.diagonal().copy()

    return dict(nodes=nodes, edges=edges, n=n, m=m, B=B, L=L, D=D, A=A, Q=Q,
                Lt=Lt, T=T, Tconn=Tconn, LT=LT, l2G=l2G, phi=phi, deg=deg,
                l2T=(ce.lambda2(T) if Tconn else None))


def restricted_min_geneig(M, S, constraint):
    """Smallest generalized eigenvalue of (M, S) on  constraint ⟂  (vector).
    Builds an orthonormal basis of constraint^perp and solves the reduced
    symmetric-definite problem. Assumes S positive definite on that subspace."""
    n = M.shape[0]
    c = constraint / np.linalg.norm(constraint)
    # orthonormal basis of c^perp
    _, _, Vt = np.linalg.svd(np.outer(c, c))
    P = Vt[1:].T                               # n x (n-1), columns span c^perp
    Mr = P.T @ M @ P
    Sr = P.T @ S @ P
    w = _sym_geneig(Mr, Sr)
    return float(np.min(w)), float(np.sort(w)[1] if len(w) > 1 else w[0])


def _sym_geneig(M, S):
    """Eigenvalues of M x = lam S x (S PD) via Cholesky whitening."""
    Lc = np.linalg.cholesky(S)
    Y = np.linalg.solve(Lc, np.linalg.solve(Lc, M).T).T  # Lc^-1 M Lc^-T
    Y = 0.5 * (Y + Y.T)
    return np.linalg.eigvalsh(Y)


# --------------------------------------------------------------------------- #
# per-graph analysis of the three strategies
# --------------------------------------------------------------------------- #
def analyse(G):
    o = operators(G)
    if not o["Tconn"] or o["l2T"] is None or o["l2T"] <= TOL:
        return None
    n, m = o["n"], o["m"]
    L, Lt, Q, A, D = o["L"], o["Lt"], o["Q"], o["A"], o["D"]
    l2G, l2T, phi, deg = o["l2G"], o["l2T"], o["phi"], o["deg"]
    B, LT = o["B"], o["LT"]
    Delta = int(deg.max()); delta = int(deg.min())

    # --- identity sanity check (lift) ---
    h = B.T @ phi
    id_num = abs(h @ LT @ h - phi @ Lt @ phi) < 1e-7
    id_den = abs(h @ h - phi @ Q @ phi) < 1e-7

    # degree imbalance of the true Fiedler
    S = float(deg @ phi)                       # = sum deg(v) phi(v)
    sigma2_d = float(np.var(deg))              # degree variance (population)

    # ---------- C0 : lift route sufficiency  mu(G) <= lambda2(G) ? ----------
    # mu = min_{phi ⟂ d} (phi^T L_t phi)/(phi^T Q phi).  Q is PD iff G non-bipartite.
    mu = mu_second = None
    Q_pd = np.linalg.eigvalsh(Q)[0] > 1e-9
    glob_max = None                            # global max gen-eig of (L_t,Q)
    if Q_pd:
        mu, mu_second = restricted_min_geneig(Lt, Q, deg)
        gw = _sym_geneig(Lt, Q)
        glob_max = float(np.max(gw))           # is the operator ineq global or only on d^perp?
    # route works iff mu <= l2G; lift bounds l2T from above iff l2T <= mu
    route_ok = (mu is not None) and (mu <= l2G + 1e-7)
    lift_above_l2T = (mu is not None) and (mu >= l2T - 1e-7)
    glob_ok = (glob_max is not None) and (glob_max <= l2G + 1e-7)

    # vertex-space projection of Fiedler onto d^perp: phi~ = phi - (S/|d|^2) d
    dd = deg @ deg
    phit = phi - (S / dd) * deg
    nvt = float(phit @ Q @ phit)
    RT_vproj = float(phit @ Lt @ phit) / nvt if nvt > TOL else float("inf")
    vproj_ok = RT_vproj <= l2G + 1e-7

    # ---------- S2 : Cauchy-Schwarz on degree imbalance ----------
    # project the lift of the TRUE Fiedler into 1_E^perp:  h' = h - (S/m) 1_E.
    # numerator unchanged (Laplacian kills 1_E); denominator loses S^2/m.
    num = float(phi @ Lt @ phi)                # = sum t_ab (dphi)^2
    den_proj = float(phi @ Q @ phi) - S * S / m
    RT_proj = num / den_proj if den_proj > TOL else float("inf")
    s2_exact = RT_proj <= l2G + 1e-7           # exact projected-lift bound
    # C-S certificate:  |S| <= sqrt(n)*sigma_d ;  num <= (Delta-1)*l2G
    S_bound = (n * sigma2_d) ** 0.5
    cs_ok = abs(S) <= S_bound + 1e-7
    # crude closed-form sufficient condition (uses num<=(Delta-1)l2G, den>=2delta-l2G-S^2/m)
    crude_lhs = (Delta - 1) * l2G
    crude_rhs = l2G * (2 * delta - l2G - S * S / m)   # <= l2G * den_proj lower bd
    crude_ok = crude_lhs <= crude_rhs + 1e-7

    # ---------- S1 : degree-weighted / normalized framing ----------
    # psi = phi/sqrt(deg) ; test normalized-Laplacian style bound.
    sq = np.sqrt(deg)
    # normalized signless Laplacian Q_norm = D^-1/2 Q D^-1/2 = I + D^-1/2 A D^-1/2
    Dm = np.diag(1.0 / sq)
    Lt_norm = Dm @ Lt @ Dm
    Q_norm = Dm @ Q @ Dm
    # smallest gen-eig of (Lt_norm, Q_norm) on (sqrt(deg))^perp == same mu (invariant)
    # so S1 doesn't change mu; instead test the *bound*  L_t <= (Delta-1) L_G  and
    # the normalized comparison  L_t_norm <= (Delta-1) L_norm.
    Lnorm = Dm @ L @ Dm                        # not the standard one (D^-1/2), but matches scaling
    # operator bound quality:  largest gen-eig of (L_t, L_G)  == max edge t_ab? test
    # rho = max over phi of (phi^T L_t phi)/(phi^T L_G phi)
    try:
        rho = float(np.max(_sym_geneig(Lt, L + 1e-12 * np.eye(n))))
    except Exception:
        rho = float("nan")

    return dict(
        n=n, m=m, Delta=Delta, delta=delta, l2G=l2G, l2T=l2T, Q=l2G / l2T,
        id_num=id_num, id_den=id_den, S=S, sigma2_d=sigma2_d, S_bound=S_bound,
        cs_ok=cs_ok, mu=mu, route_ok=route_ok, lift_above_l2T=lift_above_l2T,
        RT_proj=RT_proj, s2_exact=s2_exact, crude_ok=crude_ok, rho=rho,
        glob_max=glob_max, glob_ok=glob_ok, RT_vproj=RT_vproj, vproj_ok=vproj_ok,
        Q_pd=Q_pd, regular=(Delta == delta),
        edges=sorted(tuple(sorted(e)) for e in G.edges()),
    )


# --------------------------------------------------------------------------- #
# diverse tightest-irregular test set
# --------------------------------------------------------------------------- #
def test_graphs():
    """Curated + searched diverse irregular graphs with small Q (tight for B)."""
    out = []

    def add(name, G):
        if G.number_of_nodes() >= 3 and nx.is_connected(G):
            out.append((name, G))

    # complete graphs minus k edges (the tightest irregular family)
    for n in range(6, 11):
        K = nx.complete_graph(n)
        edges = list(K.edges())
        for k in (1, 2, 3):
            G = nx.Graph(); G.add_nodes_from(range(n))
            G.add_edges_from(edges[k:])         # drop first k edges
            add(f"K{n}-minus{k}e", G)
        # remove a star (one low-degree vertex)
        G = nx.complete_graph(n)
        for j in range(2, n):
            G.remove_edge(0, j)
        add(f"K{n}-star0", G)

    # complete multipartite (irregular partitions)
    for parts in ([4, 3], [5, 3], [4, 4, 1], [5, 2, 2], [3, 3, 2], [6, 3],
                  [4, 3, 2], [5, 4]):
        add(f"Kmulti{parts}", nx.complete_multipartite_graph(*parts))

    # split graphs / clique + pendant structures, threshold-ish
    for n in (7, 8, 9):
        G = nx.complete_graph(n - 1)
        G.add_edge(n - 1, 0)                    # one pendant onto a clique
        add(f"K{n-1}+pendant", G)
        G2 = nx.complete_graph(n - 1)
        G2.add_edges_from([(n - 1, 0), (n - 1, 1)])
        add(f"K{n-1}+deg2", G2)

    # dense random irregular graphs (denser => T(G) connected), keep diverse
    rng = np.random.default_rng(7)
    seen = set()
    cand = []
    for _ in range(4000):
        n = int(rng.integers(7, 11))
        p = float(rng.uniform(0.6, 0.95))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G) or ce.is_regular(G):
            continue
        T = ce.triangle_graph(G)
        if T.number_of_nodes() < 2 or not nx.is_connected(T):
            continue
        l2T = ce.lambda2(T); l2G = ce.lambda2(G)
        if l2T <= TOL:
            continue
        Qv = l2G / l2T
        key = (n, G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key in seen:
            continue
        seen.add(key)
        cand.append((Qv, G))
    cand.sort(key=lambda x: x[0])
    for i, (Qv, G) in enumerate(cand[:30]):
        add(f"rand-tight{i}-Q{Qv:.3f}", G)

    return out


# --------------------------------------------------------------------------- #
def main():
    print("building test set...")
    graphs = test_graphs()
    rows = []
    for name, G in graphs:
        r = analyse(G)
        if r is None:
            continue
        r["name"] = name
        rows.append(r)
    irr = [r for r in rows if not r["regular"]]
    irr.sort(key=lambda r: r["Q"])
    print(f"  {len(rows)} analysed ({len(irr)} irregular)")

    # ---- aggregate strategy verdicts ----
    n = len(rows)
    n_route = sum(1 for r in rows if r["route_ok"])
    n_liftok = sum(1 for r in rows if r["lift_above_l2T"])
    n_s2 = sum(1 for r in rows if r["s2_exact"])
    n_crude = sum(1 for r in rows if r["crude_ok"])
    n_cs = sum(1 for r in rows if r["cs_ok"])
    n_glob = sum(1 for r in rows if r["glob_ok"])
    n_vproj = sum(1 for r in rows if r["vproj_ok"])
    ids = all(r["id_num"] and r["id_den"] for r in rows)

    # worst (smallest) margins
    def margin_route(r):
        return r["l2G"] - r["mu"] if r["mu"] is not None else float("nan")
    worst_route = min((margin_route(r) for r in rows if r["mu"] is not None),
                      default=float("nan"))
    worst_s2 = min((r["l2G"] - r["RT_proj"] for r in rows
                    if np.isfinite(r["RT_proj"])), default=float("nan"))
    max_rho = max((r["rho"] for r in rows if np.isfinite(r["rho"])),
                  default=float("nan"))

    print("\n=== strategy verdicts (over %d graphs) ===" % n)
    print("identities hold:", ids)
    print(f"C0 lift route  mu<=l2G        : {n_route}/{n} (worst margin l2G-mu={worst_route:+.4f})")
    print(f"   lift bounds l2T (mu>=l2T)  : {n_liftok}/{n}")
    print(f"S2 projected-lift RT'<=l2G    : {n_s2}/{n} (worst margin {worst_s2:+.4f})")
    print(f"S2 crude closed-form          : {n_crude}/{n}")
    print(f"S2 vertex-proj Fiedler<=l2G   : {n_vproj}/{n}")
    print(f"   C-S |S|<=sqrt(n)sigma_d    : {n_cs}/{n}")
    print(f"GLOBAL op ineq (no d-restrict): {n_glob}/{n}  (if < n, the d^perp restriction is ESSENTIAL)")
    print(f"S3 max gen-eig (L_t,L_G) rho  : {max_rho:.4f}  (<= Delta-1 ?)")
    print("\ntightest 12 irregular:")
    print("  name                         n  m   Q     l2T   l2G    mu    RT'   route s2")
    for r in irr[:12]:
        print(f"  {r['name']:28s} {r['n']:2d} {r['m']:3d} {r['Q']:.3f} "
              f"{r['l2T']:.3f} {r['l2G']:.3f} "
              f"{(r['mu'] if r['mu'] else float('nan')):.3f} {r['RT_proj']:.3f} "
              f"{'Y' if r['route_ok'] else 'N':>5s} {'Y' if r['s2_exact'] else 'N'}")

    # stash results for the report writer
    main.rows = rows
    main.irr = irr
    main.stats = dict(n=n, n_route=n_route, n_liftok=n_liftok, n_s2=n_s2,
                      n_crude=n_crude, n_cs=n_cs, ids=ids,
                      worst_route=worst_route, worst_s2=worst_s2, max_rho=max_rho)


if __name__ == "__main__":
    main()
