"""
Conjecture B proof v3 — attacking the open core (DEG').

Open core (from v2), unit Fiedler f (L_G f = l2 f, f⟂1, ||f||=1), d = degrees,
disc(v) = sum_{b~v}(d_b - d_v),  S = sum_v d_v f_v,  m = |E|:

  (DEG')   (1/2) sum_v f_v^2 disc(v)  -  (1/2) sum_{ab} |d_a-d_b|(f_a-f_b)^2
           <=  l2 (f^T D f - l2 + 1 - S^2/m).

Algebraic simplification proved by hand and checked here:
  E_disc := sum_v f_v^2 disc(v) = sum_{ab in E} (d_b-d_a)(f_a^2 - f_b^2)
  => (1/2)E_disc - (1/2)E_grad = - sum_{ab in E} |d_a-d_b| f_h (f_h - f_l)
     where h = higher-degree endpoint, l = lower-degree endpoint of edge ab.
  So LHS(DEG') = sum_{ab} |d_a-d_b| f_h (f_l - f_h).

This script (1) verifies that simplification; (2) tests RHS sign; (3) tests a
battery of candidate SUFFICIENT closing inequalities; (4) records the user's
f^T A f / lambda_max(A) relations.  All on the 52 tightest irregular graphs and
a broad sweep.

Run:  python conjecture_B_proof_v3_explore.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce

TOL = 1e-9


def analyse(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}
    edges = list(G.edges()); n, m = len(nodes), len(edges)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    D = np.diag(L.diagonal()); A = D - L; d = L.diagonal().copy()
    T = ce.triangle_graph(G)
    if T.number_of_nodes() < 2 or not nx.is_connected(T):
        return None
    l2T = ce.lambda2(T)
    if l2T <= TOL:
        return None
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1].copy()
    if abs(np.linalg.norm(f) - 1) > 1e-6:
        f = f / np.linalg.norm(f)
    Delta = int(d.max()); delta = int(d.min())

    S = float(d @ f); fDf = float((d * f * f).sum())
    fAf = float(f @ A @ f)
    lamA = float(np.linalg.eigvalsh(A)[-1])     # lambda_max(A)

    # disc(v) and the two energies
    disc = (A @ d) - d * d                       # (A d)_v - d_v^2 = sum_{b~v}(d_b-d_v)
    E_disc = float((f * f) @ disc)
    E_grad = 0.0
    LHS_simpl = 0.0
    cs_a = 0.0                                    # sum |d_a-d_b| f_h^2  (for Cauchy-Schwarz)
    for u, v in edges:
        i, j = idx[u], idx[v]
        gap = abs(d[i] - d[j])
        E_grad += gap * (f[i] - f[j]) ** 2
        # higher/lower degree endpoint
        if d[i] >= d[j]:
            h, lo = i, j
        else:
            h, lo = j, i
        LHS_simpl += gap * f[h] * (f[lo] - f[h])
        cs_a += gap * f[h] ** 2

    # cross-check the identity E_disc = sum_{ab}(d_b-d_a)(f_a^2-f_b^2)
    E_disc_alt = 0.0
    for u, v in edges:
        i, j = idx[u], idx[v]
        E_disc_alt += (d[j] - d[i]) * (f[i] ** 2 - f[j] ** 2)

    LHS = 0.5 * E_disc - 0.5 * E_grad
    RHS = l2 * (fDf - l2 + 1.0 - S * S / m)

    # ---- candidate sufficient closing inequalities ----
    # C1: LHS <= 0  (discrepancy energy dominated by gradient penalty)
    c1 = LHS <= 1e-9
    # C2: Cauchy-Schwarz  |LHS| <= sqrt(cs_a)*sqrt(E_grad) <= RHS
    cs_bound = (cs_a * E_grad) ** 0.5
    c2 = cs_bound <= RHS + 1e-9
    # C3: RHS >= 0 (needed for C1 to close)
    c3 = RHS >= -1e-9
    # C4: user's chain — lower bound fDf via fAf >= -lamA (since f^T A f >= lambda_min)
    #     RHS >= l2(delta - l2 + 1 - S^2/m); test that this weaker RHS still >= LHS
    RHS_weak = l2 * (delta - l2 + 1.0 - S * S / m)
    c4 = LHS <= RHS_weak + 1e-9
    # C5: drop the gradient penalty AND S^2/m (cleanest): (1/2)E_disc <= l2(fDf-l2+1)
    c5 = 0.5 * E_disc <= l2 * (fDf - l2 + 1.0) + 1e-9

    return dict(n=n, m=m, Delta=Delta, delta=delta, l2=l2, l2T=l2T, Q=l2 / l2T,
                S=S, fDf=fDf, fAf=fAf, lamA=lamA,
                E_disc=E_disc, E_disc_err=abs(E_disc - E_disc_alt),
                E_grad=E_grad, LHS=LHS, LHS_simpl_err=abs(LHS - LHS_simpl),
                RHS=RHS, deg_prime=(LHS <= RHS + 1e-7),
                c1=c1, c2=c2, c3=c3, c4=c4, c5=c5, cs_bound=cs_bound,
                regular=(Delta == delta))


def tight_graphs():
    out = []

    def add(name, G):
        if G.number_of_nodes() >= 3 and nx.is_connected(G):
            out.append((name, G))
    for n in range(6, 11):
        K = nx.complete_graph(n); E = list(K.edges())
        for k in (1, 2, 3):
            G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E[k:])
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


def broad_graphs(n_target=2500):
    out = []; rng = np.random.default_rng(2024); seen = set()
    for n in range(6, 12):
        K = nx.complete_graph(n); E = list(K.edges())
        for k in range(1, 9):
            G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E[k:])
            out.append((f"K{n}-m{k}", G))
    while len(out) < n_target:
        n = int(rng.integers(6, 12)); p = float(rng.uniform(0.45, 0.97))
        G = nx.gnp_random_graph(n, p, seed=int(rng.integers(0, 2**31)))
        if not nx.is_connected(G):
            continue
        key = (n, G.number_of_edges(), nx.weisfeiler_lehman_graph_hash(G, iterations=2))
        if key in seen:
            continue
        seen.add(key); out.append((f"rand{n}", G))
    return out


def summarize(rows, label):
    N = len(rows)
    def cnt(k): return sum(1 for r in rows if r[k])
    id_disc = max(r["E_disc_err"] for r in rows)
    id_lhs = max(r["LHS_simpl_err"] for r in rows)
    print(f"\n=== {label}: {N} graphs ===")
    print(f"identity E_disc = sum(d_b-d_a)(f_a^2-f_b^2): max err {id_disc:.2e}")
    print(f"identity (1/2)E_disc-(1/2)E_grad = -sum|d_a-d_b|f_h(f_h-f_l): max err {id_lhs:.2e}")
    print(f"(DEG') LHS<=RHS                : {cnt('deg_prime')}/{N}")
    print(f"C1  LHS<=0 (disc<=grad penalty): {cnt('c1')}/{N}")
    print(f"C2  Cauchy-Schwarz <= RHS      : {cnt('c2')}/{N}")
    print(f"C3  RHS>=0                     : {cnt('c3')}/{N}")
    print(f"C4  LHS<=l2(delta-l2+1-S^2/m)  : {cnt('c4')}/{N}")
    print(f"C5  (1/2)E_disc<=l2(fDf-l2+1)  : {cnt('c5')}/{N}")
    # diagnostics on LHS sign
    pos = [r for r in rows if r["LHS"] > 1e-9]
    print(f"graphs with LHS>0 (C1 fails)  : {len(pos)}")
    if pos:
        worst = max(pos, key=lambda r: r["LHS"] - r["RHS"])
        print(f"  worst LHS-RHS among them    : {worst['LHS']-worst['RHS']:+.4f} "
              f"(LHS={worst['LHS']:.4f} RHS={worst['RHS']:.4f} n={worst['n']} Q={worst['Q']:.3f})")


def main():
    tight = [r for r in (analyse(G) for _, G in tight_graphs()) if r]
    broad = [r for r in (analyse(G) for _, G in broad_graphs()) if r]
    summarize(tight, "tightest irregular")
    summarize(broad, "broad sweep")
    main.tight = tight; main.broad = broad


if __name__ == "__main__":
    main()
