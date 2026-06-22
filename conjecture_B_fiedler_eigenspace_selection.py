"""
lam2 eigenspace selection: gap(f) = f^T M f - lam^2 (||f||=1) on E_{lam2}.
M = lam(2D - dd^T/m) - L_t  (gap = f^T M f - lam^2 over unit sphere; lam^2 const).
Existential condition: max over E_{lam2} of (f^T M f) - lam^2 >= 0, i.e. lam_max(M|E) >= lam^2.
Test: hTconn (triangleGraph connected) <=> lam_max(M|E) - lam^2 >= 0 ?
Run: python conjecture_B_fiedler_eigenspace_selection.py
"""
import numpy as np
import networkx as nx


def triangle_graph(G):
    E = list(G.edges()); TG = nx.Graph(); TG.add_nodes_from(range(len(E)))
    for a in range(len(E)):
        for b in range(a + 1, len(E)):
            s1 = set(E[a]); s2 = set(E[b]); common = s1 & s2
            if len(common) == 1:
                x = common.pop(); p = (s1 - {x}).pop(); q = (s2 - {x}).pop()
                if G.has_edge(p, q): TG.add_edge(a, b)
    return TG


def Mgap(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]
    Eidx = [k for k in range(n) if abs(ev[k] - lam) < 1e-7]
    E = U[:, Eidx]               # n x mult, orthonormal basis of E_{lam2}
    m = G.number_of_edges(); A2 = A @ A
    Lt = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if A[i, j] > 0: Lt[i, j] = -A2[i, j]
    for i in range(n): Lt[i, i] = -sum(Lt[i, j] for j in range(n) if j != i)
    M = lam * (2 * np.diag(d) - np.outer(d, d) / m) - Lt
    Mr = E.T @ M @ E             # restriction to E_{lam2}
    evr = np.linalg.eigvalsh(Mr)
    # gap range over unit sphere in E: evr - lam^2
    return dict(n=n, lam=lam, mult=len(Eidx), gmin=evr.min() - lam ** 2, gmax=evr.max() - lam ** 2,
                lam2=lam ** 2, lmaxMr=evr.max())


def corpus():
    out = []
    def star(kc, ks):
        G = nx.complete_graph(kc)
        for i in range(ks): G.add_edge(0, kc + i)
        return G
    def pend(kc, ks):
        G = nx.complete_graph(kc)
        for i in range(ks): G.add_edge(i % kc, kc + i)
        return G
    def deg2dense(nn, q=0.6, s=1):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
        H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    out += [("K12+star15", star(12, 15)), ("K8+star10", star(8, 10)), ("K20+star40", star(20, 40)),
            ("K12+pend30", pend(12, 30)), ("K10+pend25", pend(10, 25)), ("K15+pend40", pend(15, 40)),
            ("Kbip6_6", nx.complete_bipartite_graph(6, 6)), ("Kbip8_8", nx.complete_bipartite_graph(8, 8)),
            ("cocktail2x5", nx.complete_multipartite_graph(*([2] * 5))),
            ("petersen", nx.petersen_graph()), ("hypercubeQ4", nx.hypercube_graph(4)),
            ("rr20_6", nx.random_regular_graph(6, 20, seed=1)), ("K20", nx.complete_graph(20)),
            ("deg2dense40", deg2dense(40)), ("deg2dense80", deg2dense(80)),
            ("gnp20_.6", nx.gnp_random_graph(20, 0.6, seed=3))]
    # extra pendant variants to probe the disconnected-triangleGraph boundary
    out += [("K8+pend4", pend(8, 4)), ("K8+pend1", pend(8, 1)), ("K6+pend12", pend(6, 12))]
    return [(nm, G) for nm, G in out if nx.is_connected(G)]


def main():
    print("=" * 96)
    print("TASK 1/2/3 — gap(f) on E_{lam2}: M_gap restriction; max gap = lam_max(M|E) - lam²; vs hTconn")
    print("=" * 96)
    print(f"  {'graph':14s} {'n':>4} {'lam2':>8} {'mult':>5} {'min gap':>10} {'max gap':>10} "
          f"{'TG-conn':>8} {'∃ holds':>8}")
    rows = []
    for nm, G in corpus():
        q = Mgap(G); TG = triangle_graph(G)
        tgc = nx.is_connected(TG) if TG.number_of_nodes() > 0 else False
        holds = q['gmax'] >= -1e-7
        rows.append((nm, q, tgc, holds))
        print(f"  {nm:14s} {q['n']:4d} {q['lam']:8.4f} {q['mult']:5d} {q['gmin']:10.4f} {q['gmax']:10.4f} "
              f"{str(tgc):>8} {str(holds):>8}")

    print("\n" + "=" * 96)
    print("TASK 3 — correlation: does TG-connected ⟺ max gap ≥ 0 (∃ holds)?")
    print("=" * 96)
    tc_hold = sum(1 for _, _, tgc, h in rows if tgc and h)
    tc_fail = sum(1 for _, _, tgc, h in rows if tgc and not h)
    nc_hold = sum(1 for _, _, tgc, h in rows if not tgc and h)
    nc_fail = sum(1 for _, _, tgc, h in rows if not tgc and not h)
    print(f"  TG-connected & ∃ holds : {tc_hold}")
    print(f"  TG-connected & ∃ FAILS : {tc_fail}   <- would break hTconn→∃")
    print(f"  TG-disconnected & ∃ holds : {nc_hold}")
    print(f"  TG-disconnected & ∃ FAILS : {nc_fail}")
    print(f"  => hTconn ⟹ ∃ holds : {'CONFIRMED' if tc_fail == 0 else 'VIOLATED'}")

    print("\n" + "=" * 96)
    print("TASK 4 — failure cases (∃ fails): are they ALL triangleGraph-disconnected?")
    print("=" * 96)
    fails = [(nm, q, tgc) for nm, q, tgc, h in rows if not h]
    for nm, q, tgc in fails:
        print(f"  {nm:14s} max gap={q['gmax']:.4f}  TG-connected={tgc}")
    print(f"  all ∃-failures have TG disconnected: {all(not tgc for _, _, tgc in fails)}")

    print("\n" + "=" * 96)
    print("TASK 5 — structural: does TG-connectivity force a positive direction in E_{lam2}?")
    print("=" * 96)
    print("  Probe: for TG-connected graphs, the K_n-like 'good' direction (high |f| on dense core)")
    print("  achieves gap>=0. min mult among TG-connected & holds; do simple-lam2 always hold?")
    simple_hold = sum(1 for _, q, tgc, h in rows if q['mult'] == 1 and h)
    simple_all = sum(1 for _, q, _, _ in rows if q['mult'] == 1)
    print(f"  simple-λ₂ (mult=1) graphs: {simple_all}; of these ∃/∀ holds: {simple_hold}")
    print(f"  (simple λ₂ ⟹ gap is a single scalar; ∃=∀; holds iff conjecture gap≥0)")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  hTconn⟹∃: {'CONFIRMED' if tc_fail==0 else 'VIOLATED'}; all ∃-failures TG-disconnected: "
          f"{all(not tgc for _,_,tgc in fails) if fails else True}")


if __name__ == "__main__":
    main()
