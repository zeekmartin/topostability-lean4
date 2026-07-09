"""
Li-Ji technique transfer test for Conjecture B.

Li-Ji (arXiv 2607.03711) prove the Laplacian Spread Conjecture from the
matrix inequality  (n-1) L_G  >=  L_{A^[2]}  , whose engine is the expansion
    ||L_G z||^2 = z^T L_G^2 z >= 0
combined with the zero-row-sum identity  z^T M z = sum_{i<j} (-m_ij)(z_i-z_j)^2
and the entrywise fact  (L^2)_ij = -a_ij(d_i+d_j) + c_ij   (i != j),
                        (L^2)_ii = d_i(d_i+1).

Conjecture B:  lambda_2(T(G)) <= lambda_2(G),  T(G) = triangle (line-of-triangles)
graph on the EDGES of G:  two edges adjacent in T(G) iff they lie in a common
triangle of G.  The remaining Lean 'sorry' is the aggregate triangle Poincare
    sum_e t_e (f_a-f_b)^2  <=  2 lambda sum_v d_v f_v^2,       t_e = #triangles on e.

This script tests whether the Li-Ji "expand ||L z||^2, no test vector" engine,
lifted to edge space via the oriented incidence matrix B (m x n,
B_{e,v}=+1 head, -1 tail, so L_G = B^T B), controls the T(G) form.

Objects (edge space, dimension m):
    M2 := B L^2 B^T          (Li-Ji operator lifted to edges;  h^T M2 h = ||L B^T h||^2)
    L_T := Laplacian of T(G)
    lift  h = B f            (edge-difference lift of a vertex vector f: h_e = f_a - f_b)

Entry formula derived & verified (Task 1):
    (B L^2 B^T)_{e,e'} = (L^2)_ac - (L^2)_ad - (L^2)_bc + (L^2)_bd,  e=(a,b), e'=(c,d)
    diagonal:  (B L^2 B^T)_{e,e} = d_a^2 + d_b^2 + 3(d_a+d_b) - 2 t_e     (t_e = c_ab)

Run:  python liji_transfer_test.py
"""
import numpy as np
import networkx as nx


# ----------------------------------------------------------------------------
# core linear algebra
# ----------------------------------------------------------------------------
def edge_list(G):
    return [tuple(sorted(e)) for e in G.edges()]


def incidence(G, edges):
    """Oriented incidence B (m x n): B_{e,v}=+1 head (a), -1 tail (b), e=(a,b)."""
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    m, n = len(edges), len(nodes)
    B = np.zeros((m, n))
    for k, (a, b) in enumerate(edges):
        B[k, idx[a]] = +1.0
        B[k, idx[b]] = -1.0
    return B, nodes, idx


def triangle_graph(G, edges):
    """T(G): nodes = edges of G (in the given order), adjacency iff shared triangle."""
    idx = {e: k for k, e in enumerate(edges)}
    m = len(edges)
    A = np.zeros((m, m))
    # for every triangle, its 3 edges are mutually adjacent in T(G)
    for u, v, w in _triangles(G):
        e1 = tuple(sorted((u, v)))
        e2 = tuple(sorted((u, w)))
        e3 = tuple(sorted((v, w)))
        for x, y in ((e1, e2), (e1, e3), (e2, e3)):
            A[idx[x], idx[y]] = 1.0
            A[idx[y], idx[x]] = 1.0
    L_T = np.diag(A.sum(1)) - A
    return A, L_T


def _triangles(G):
    seen = set()
    out = []
    for u in G:
        for v in G[u]:
            if v <= u:
                continue
            for w in set(G[u]) & set(G[v]):
                if w <= v:
                    continue
                key = tuple(sorted((u, v, w)))
                if key not in seen:
                    seen.add(key)
                    out.append(key)
    return out


def triangle_count_per_edge(G, edges):
    """t_e = number of triangles containing edge e = #common neighbours of its endpoints."""
    adj = {v: set(G[v]) for v in G}
    return np.array([len(adj[a] & adj[b]) for (a, b) in edges], dtype=float)


# ----------------------------------------------------------------------------
# Task 1: verify the entrywise formula for B L^2 B^T
# ----------------------------------------------------------------------------
def verify_entry_formula(G):
    edges = edge_list(G)
    B, nodes, idx = incidence(G, edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    L2 = L @ L
    d = L.diagonal()
    A = np.diag(d) - L
    A2 = A @ A                      # (A^2)_ij = common neighbours c_ij (i!=j), d_i (i=i)
    M2 = B @ L2 @ B.T

    # predicted entries from (L^2)_ij formula
    m = len(edges)
    pred = np.zeros((m, m))
    for e, (a, b) in enumerate(edges):
        ia, ib = idx[a], idx[b]
        for ep, (c, dd) in enumerate(edges):
            ic, idd = idx[c], idx[dd]
            pred[e, ep] = L2[ia, ic] - L2[ia, idd] - L2[ib, ic] + L2[ib, idd]
    err_expand = float(np.max(np.abs(M2 - pred)))

    # closed-form diagonal:  d_a^2 + d_b^2 + 3(d_a+d_b) - 2 t_e
    t = triangle_count_per_edge(G, edges)
    diag_pred = np.array([d[idx[a]] ** 2 + d[idx[b]] ** 2
                          + 3 * (d[idx[a]] + d[idx[b]]) - 2 * t[e]
                          for e, (a, b) in enumerate(edges)])
    err_diag = float(np.max(np.abs(np.diag(M2) - diag_pred)))
    return err_expand, err_diag


# ----------------------------------------------------------------------------
# Tasks 2/3/4: the quantities on Fiedler lifts + matrix domination
# ----------------------------------------------------------------------------
def quantities(G):
    edges = edge_list(G)
    B, nodes, idx = incidence(G, edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    L2 = L @ L
    d = L.diagonal()
    ev, V = np.linalg.eigh(L)
    lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])          # unit-norm Fiedler
    A_T, L_T = triangle_graph(G, edges)
    t = triangle_count_per_edge(G, edges)

    M2 = B @ L2 @ B.T                              # Li-Ji operator on edge space
    h = B @ f                                       # edge-difference lift, h_e = f_a - f_b

    a = float(h @ M2 @ h)                           # (a) ||L B^T h||^2 = f^T L^4 f (=lam^4 on Fiedler)
    b = float(h @ L_T @ h)                          # (b) T(G) Dirichlet energy of the lift
    hh = float(h @ h)                               # = f^T L f = lam (unit f)
    c = lam * hh                                    # (c) Conjecture-B RHS scale
    tri_diag = float((t * h * h).sum())             # the ACTUAL aggregate-triangle LHS: sum_e t_e h_e^2
    Dff = float((d * f * f).sum())                  # sum_v d_v f_v^2
    poincare_rhs = 2.0 * lam * Dff                  # aggregate triangle Poincare RHS

    # matrix domination on the CUT SPACE (image of B): min_{f _|_ 1} f^T L^4 f / f^T (B^T L_T B) f
    M1 = L @ L @ L @ L                              # L^4 (kernel = span 1)
    Mden = B.T @ L_T @ B                            # B^T L_T B  (n x n)
    Cc = generalized_min_on_complement(M1, Mden, ones=np.ones(len(nodes)))

    # domination of the DIAGONAL triangle form by M2 on lifts:
    #   min_{f _|_ 1} f^T L^4 f / f^T (B^T diag(t) B) f
    Mdiag = B.T @ np.diag(t) @ B
    Cdiag = generalized_min_on_complement(M1, Mdiag, ones=np.ones(len(nodes)))

    return dict(
        n=G.number_of_nodes(), m=len(edges), lam=lam,
        a=a, b=b, c=c, hh=hh,
        ratio_ab=(a / b if b > 1e-12 else np.inf),
        ratio_bc=(b / c if c > 1e-12 else np.inf),
        tri_diag=tri_diag, poincare_rhs=poincare_rhs,
        poincare_slack=poincare_rhs - tri_diag,          # >=0 iff the sorry holds here
        # on Fiedler lift, a should equal lam^4 exactly:
        a_minus_lam4=a - lam ** 4,
        C_cut=Cc,                                        # domination const on all lifts (full L_T)
        C_diag=Cdiag,                                    # domination const on all lifts (diag t form)
        # Li-Ji scale in vertex space for reference
        nm1=G.number_of_nodes() - 1,
    )


def generalized_min_on_complement(Mnum, Mden, ones):
    """min over f _|_ ones of (f^T Mnum f)/(f^T Mden f), both PSD.

    Correct even when Mden is singular on ones^perp: directions in ker(Mden)
    are eliminated by a Schur complement of Mnum (moving toward them only
    RAISES the ratio, so they contribute the Schur correction, not a 0).
    Returns inf if Mden ~ 0 on the whole complement.
    """
    n = len(ones)
    q = ones / np.linalg.norm(ones)
    _, _, Vt = np.linalg.svd(np.eye(n) - np.outer(q, q))
    Q = Vt[:n - 1].T                                   # basis of ones^perp
    An = 0.5 * (Q.T @ Mnum @ Q + (Q.T @ Mnum @ Q).T)
    Ad = 0.5 * (Q.T @ Mden @ Q + (Q.T @ Mden @ Q).T)
    ev, U = np.linalg.eigh(Ad)
    if ev[-1] < 1e-12:
        return np.inf
    tol = 1e-9 * ev[-1]
    Rmask, Kmask = ev > tol, ev <= tol                 # range / kernel of Ad
    AnU = U.T @ An @ U
    An_RR = AnU[np.ix_(Rmask, Rmask)]
    if Kmask.any():                                    # Schur-complement out ker(Ad)
        An_RK = AnU[np.ix_(Rmask, Kmask)]
        An_KK = AnU[np.ix_(Kmask, Kmask)]
        S = An_RR - An_RK @ np.linalg.pinv(An_KK) @ An_RK.T
    else:
        S = An_RR
    s = 1.0 / np.sqrt(ev[Rmask])
    R = 0.5 * (S * s[:, None] * s[None, :] + (S * s[:, None] * s[None, :]).T)
    return float(np.linalg.eigvalsh(R)[0])


# ----------------------------------------------------------------------------
# corpus
# ----------------------------------------------------------------------------
def deg2dense(n):
    G = nx.cycle_graph(n)
    for i in range(0, n, 2):
        G.add_edge(i, (i + 2) % n)
    return G


def twin(n):
    G = nx.complete_graph(n)
    G.add_node(n); G.add_node(n + 1)
    for v in range(n):
        G.add_edge(n, v); G.add_edge(n + 1, v)
    return G


def corpus():
    gs = []
    gs.append(("K6", nx.complete_graph(6)))
    gs.append(("K10", nx.complete_graph(10)))
    gs.append(("gnp_20_0.3", nx.gnp_random_graph(20, 0.3, seed=1)))
    gs.append(("gnp_30_0.25", nx.gnp_random_graph(30, 0.25, seed=2)))
    gs.append(("deg2dense_12", deg2dense(12)))
    gs.append(("twin_6", twin(6)))
    gs.append(("lollipop_6_4", nx.lollipop_graph(6, 4)))
    gs.append(("lollipop_8_2", nx.lollipop_graph(8, 2)))
    gs.append(("barbell_5_1", nx.barbell_graph(5, 1)))
    gs.append(("barbell_6_3", nx.barbell_graph(6, 3)))
    gs.append(("wheel_10", nx.wheel_graph(10)))
    gs.append(("wheel_16", nx.wheel_graph(16)))
    gs.append(("regular_3_12", nx.random_regular_graph(3, 12, seed=3)))
    gs.append(("regular_4_14", nx.random_regular_graph(4, 14, seed=4)))
    gs.append(("petersen", nx.petersen_graph()))
    gs.append(("cube_Q3", nx.hypercube_graph(3)))
    gs.append(("icosahedral", nx.icosahedral_graph()))
    gs.append(("octahedral", nx.octahedral_graph()))
    # relabel non-integer-labelled graphs
    out = []
    for name, G in gs:
        G = nx.convert_node_labels_to_integers(G)
        if G.number_of_nodes() >= 4 and nx.is_connected(G):
            out.append((name, G))
    return out


def main():
    print("=" * 84)
    print("TASK 1 — entrywise formula for B L^2 B^T  (want machine zero on both)")
    print("=" * 84)
    for name, G in corpus()[:6]:
        ee, ed = verify_entry_formula(G)
        print(f"  {name:16s}  expand-err={ee:.2e}   diag-closedform-err={ed:.2e}")

    print()
    print("=" * 84)
    print("TASKS 2/3/4 — quantities on Fiedler lifts + matrix domination")
    print("=" * 84)
    print(f"{'graph':16s} {'lam':>7s} {'(a)ML2M':>10s} {'(b)L_T':>9s} "
          f"{'(c)RHS':>8s} {'a/b':>8s} {'b/c':>7s} {'C_cut':>8s} {'C_diag':>8s} {'Poin?':>6s}")
    rows = []
    for name, G in corpus():
        q = quantities(G)
        rows.append((name, q))
        poin = "OK" if q['poincare_slack'] >= -1e-9 else "FAIL"
        print(f"{name:16s} {q['lam']:7.3f} {q['a']:10.3f} {q['b']:9.3f} "
              f"{q['c']:8.3f} {q['ratio_ab']:8.3f} {q['ratio_bc']:7.3f} "
              f"{q['C_cut']:8.3f} {q['C_diag']:8.3f} {poin:>6s}")

    # aggregate summary
    ab = np.array([q['ratio_ab'] for _, q in rows])
    bc = np.array([q['ratio_bc'] for _, q in rows])
    Ccut = np.array([q['C_cut'] for _, q in rows])
    Cdiag = np.array([q['C_diag'] for _, q in rows])
    a4 = np.array([abs(q['a_minus_lam4']) for _, q in rows])
    poin = np.array([q['poincare_slack'] for _, q in rows])

    print()
    print("=" * 84)
    print("SUMMARY")
    print("=" * 84)
    print(f"  graphs analysed                         : {len(rows)}")
    print(f"  |(a) - lam^4| on Fiedler lift  (max)    : {a4.max():.2e}   "
          f"(confirms a = lam^4 exactly)")
    print(f"  ratio (a)/(b) = ML2M / L_T     [min,max]: [{ab.min():.3f}, {ab.max():.3f}]")
    print(f"  ratio (b)/(c) = L_T / (lam hh) [min,max]: [{bc.min():.3f}, {bc.max():.3f}]")
    print(f"  C_cut  (M2 >= C L_T on ALL lifts) [min] : {Ccut.min():.4f}"
          f"   -> uniform lower bound across corpus")
    print(f"  C_diag (M2 >= C diag(t) on lifts) [min] : {Cdiag.min():.4f}")
    print(f"  aggregate-triangle Poincare slack [min] : {poin.min():.4f}   "
          f"({int((poin>=-1e-9).sum())}/{len(rows)} hold)")
    print("=" * 84)


if __name__ == "__main__":
    main()
