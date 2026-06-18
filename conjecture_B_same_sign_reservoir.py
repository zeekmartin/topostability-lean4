"""
Same-sign reservoir analysis for the reduced inequality  Delta + C_hard <= C_same
(equivalent to the aggregate triangle-Poincare  T <= lam2 fDf).

PROVED identity (Lean: triEnergy_sub_two_lam_degQuad):
    T - lam2 fDf = Delta + C_hard - C_same
    Delta   = sum_v (tau_v - lam2 d_v) f_v^2
    C_hard  = 2 sum_{cross-sign}  t_ab |f_a f_b|
    C_same  = 2 sum_{same-sign}   t_ab  f_a f_b      (>= 0)
    tau_v   = sum_{u~v} t_{vu}                       (twice #triangles through v)

Nodal domains  V+ = {f >= 0},  V- = {f < 0}.

TASK 1: decompose Delta, C_same, C_hard by domain; where is the fight tightest?
TASK 2: test  C_same_+  vs  sum_{v in V+} tau_v^same f_v^2  (claim is REVERSED; gap = T_++).
TASK 3: eigen lower bound  sum_{v in V+} f_v sum_{u in V+,u~v} f_u  >=  sum_{V+}(d_v-lam2)f_v^2.
TASK 4: triangle-Perron  sum_{v in V+} f_v sum_{u in V+,u~v} t_vu f_u (= C_same_+)  vs  Delta_+.

Run: python conjecture_B_same_sign_reservoir.py
"""
import numpy as np
import networkx as nx


def analyse(G):
    nodes = list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal()
    A = np.diag(d) - L
    ev, V = np.linalg.eigh(L)
    lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    M = A * A2                      # M_vu = t_vu on edges, 0 elsewhere
    tau = M.sum(1)                  # tau_v = sum_{u~v} t_vu

    pos = f >= 0.0
    neg = ~pos
    ff = np.outer(f, f)
    PP = np.outer(pos, pos)         # both in V+
    NN = np.outer(neg, neg)         # both in V-
    SAME = PP | NN
    CROSS = ~SAME

    # ---- correlation pieces (ordered sums = 2 * unordered edge sums) ----
    C_same_p = float((M * ff * PP).sum())
    C_same_n = float((M * ff * NN).sum())
    C_same = C_same_p + C_same_n
    C_hard = float(-(M * ff * CROSS).sum())     # cross f_a f_b < 0 -> negate

    # ---- diagonal ----
    diag_w = tau - lam * d
    Delta_p = float((diag_w[pos] * f[pos] ** 2).sum())
    Delta_n = float((diag_w[neg] * f[neg] ** 2).sum())
    Delta = Delta_p + Delta_n

    # ---- triangle energy split (sanity) ----
    T = float((M * (np.subtract.outer(f, f) ** 2)).sum()) / 2.0   # = sum_E t (f_a-f_b)^2
    fDf = float((d * f * f).sum())

    # ---- TASK 2: tau^same weighted f^2 within each domain ----
    tau_same = (M * SAME).sum(1)
    S2_p = float((tau_same[pos] * f[pos] ** 2).sum())   # = sum_{E(V+)} t(f_a^2+f_b^2)
    S2_n = float((tau_same[neg] * f[neg] ** 2).sum())

    # ---- TASK 3: unweighted eigen lower bound on same-sign neighbour sum ----
    nbr_pos = A @ (f * pos)         # (nbr_pos)_v = sum_{u~v, u in V+} f_u
    nbr_neg = A @ (f * neg)
    U_p = float((f[pos] * nbr_pos[pos]).sum())          # = 2 sum_{E(V+)} f_a f_b
    U_n = float((f[neg] * nbr_neg[neg]).sum())
    eig_rhs_p = float(((d[pos] - lam) * f[pos] ** 2).sum())
    eig_rhs_n = float(((d[neg] - lam) * f[neg] ** 2).sum())

    # ---- TASK 4: triangle-Perron (should equal C_same_p / C_same_n) ----
    tnbr_pos = M @ (f * pos)        # sum_{u~v,u in V+} t_vu f_u
    tnbr_neg = M @ (f * neg)
    TP_p = float((f[pos] * tnbr_pos[pos]).sum())
    TP_n = float((f[neg] * tnbr_neg[neg]).sum())

    return dict(n=len(nodes), m=int(d.sum() // 2), lam=lam,
                T=T, fDf=fDf, Q=T - lam * fDf,
                Delta=Delta, Delta_p=Delta_p, Delta_n=Delta_n,
                C_same=C_same, C_same_p=C_same_p, C_same_n=C_same_n, C_hard=C_hard,
                S2_p=S2_p, S2_n=S2_n, T_pp=S2_p - C_same_p, T_nn=S2_n - C_same_n,
                U_p=U_p, U_n=U_n, eig_rhs_p=eig_rhs_p, eig_rhs_n=eig_rhs_n,
                TP_p=TP_p, TP_n=TP_n)


# ----------------------------------------------------------- families
def glue(a, b):                      # two cliques joined by a single bridge edge
    G = nx.complete_graph(a)
    H = nx.relabel_nodes(nx.complete_graph(b), {i: i + a for i in range(b)})
    G = nx.union(G, H); G.add_edge(a - 1, a)
    return G


def chain_cliques(m, k):
    G = nx.complete_graph(m)
    for c in range(1, k):
        H = nx.relabel_nodes(nx.complete_graph(m), {i: i + c * m for i in range(m)})
        G = nx.union(G, H); G.add_edge((c - 1) * m, c * m)
    return G


def near_complete(n, drop):          # K_n minus `drop` random edges (a bottleneck-ish dense)
    G = nx.complete_graph(n)
    rng = np.random.default_rng(drop + n)
    edges = list(G.edges())
    for idx in rng.choice(len(edges), size=min(drop, len(edges)), replace=False):
        G.remove_edge(*edges[idx])
    return G


def families():
    fam = {}
    fam["barbell"] = [(f"barbell({m},{L})", nx.barbell_graph(m, L))
                      for m in (5, 10, 20, 40, 80) for L in (0, 1, 3, 8)]
    fam["lollipop"] = [(f"lollipop({m},{L})", nx.lollipop_graph(m, L))
                       for m in (5, 10, 20, 40) for L in (1, 3, 8, 20)]
    fam["glue"] = [(f"glue({a},{b})", glue(a, b))
                   for (a, b) in ((5, 5), (10, 10), (20, 20), (40, 40), (5, 40), (3, 60))]
    fam["chain_cliques"] = [(f"chain({m}x{k})", chain_cliques(m, k))
                            for (m, k) in ((10, 2), (20, 2), (40, 2), (20, 3), (15, 4))]
    fam["near_complete"] = [(f"K{n}-{drop}", near_complete(n, drop))
                            for n in (20, 40, 60) for drop in (1, 3, 10)]
    return fam


# ----------------------------------------------------------- main
def main():
    fam = families()
    print("=" * 96)
    print("TASK 1 — per-domain decomposition on near-tight families")
    print("=" * 96)
    print(f"{'graph':18s} {'lam':>7s} {'Delta+':>9s} {'Delta-':>9s} "
          f"{'Csame+':>9s} {'Csame-':>9s} {'Chard':>8s} {'Cs/Delta':>9s} {'Q':>10s}")
    tight = []
    for famname, lst in fam.items():
        for nm, G in lst:
            if not nx.is_connected(G) or G.number_of_nodes() < 4:
                continue
            r = analyse(G)
            if r['lam'] < 1e-9:
                continue
            cs_over_delta = (r['C_same'] / r['Delta']) if abs(r['Delta']) > 1e-9 else float('inf')
            print(f"{nm:18s} {r['lam']:7.4f} {r['Delta_p']:9.3f} {r['Delta_n']:9.3f} "
                  f"{r['C_same_p']:9.3f} {r['C_same_n']:9.3f} {r['C_hard']:8.3f} "
                  f"{cs_over_delta:9.3f} {r['Q']:10.2e}")
            tight.append((famname, nm, r))

    # aggregate tests across ALL near-tight graphs
    print("\n" + "=" * 96)
    print("TASK 2 — C_same_+ vs sum_{V+} tau^same f^2   (claim C_same_+ >= S2_+ is REVERSED)")
    print("=" * 96)
    ge = sum(1 for _, _, r in tight if r['C_same_p'] >= r['S2_p'] - 1e-9
             and r['C_same_n'] >= r['S2_n'] - 1e-9)
    le = sum(1 for _, _, r in tight if r['C_same_p'] <= r['S2_p'] + 1e-9
             and r['C_same_n'] <= r['S2_n'] + 1e-9)
    gap_ok = sum(1 for _, _, r in tight
                 if abs((r['S2_p'] - r['C_same_p']) - r['T_pp']) < 1e-6
                 and abs((r['S2_n'] - r['C_same_n']) - r['T_nn']) < 1e-6)
    print(f"  C_same_+ >= S2_+  (the claim) holds: {ge}/{len(tight)}")
    print(f"  C_same_+ <= S2_+  (AM-GM truth)     : {le}/{len(tight)}")
    print(f"  gap  S2_+ - C_same_+ == T_++ exactly: {gap_ok}/{len(tight)}")

    print("\n" + "=" * 96)
    print("TASK 3 — eigen lower bound:  U_+ = sum f_v sum_{V+ nbr} f_u  >=  sum_{V+}(d_v-lam)f_v^2")
    print("=" * 96)
    okp = sum(1 for _, _, r in tight if r['U_p'] >= r['eig_rhs_p'] - 1e-7)
    okn = sum(1 for _, _, r in tight if r['U_n'] >= r['eig_rhs_n'] - 1e-7)
    slack = np.array([r['U_p'] - r['eig_rhs_p'] for _, _, r in tight])
    print(f"  V+ bound holds: {okp}/{len(tight)};  V- bound holds: {okn}/{len(tight)}")
    print(f"  slack U_+ - rhs_+ : min={slack.min():.3e} median={np.median(slack):.3e} "
          f"max={slack.max():.3e}")

    print("\n" + "=" * 96)
    print("TASK 4 — triangle-Perron  TP_+ (= C_same_+)  vs  Delta_+ ;  and global closure")
    print("=" * 96)
    tp_eq = sum(1 for _, _, r in tight if abs(r['TP_p'] - r['C_same_p']) < 1e-6
                and abs(r['TP_n'] - r['C_same_n']) < 1e-6)
    print(f"  TP_+ == C_same_+ identity holds: {tp_eq}/{len(tight)}")
    # per-domain C_same_+ >= Delta_+ ?
    pd_p = sum(1 for _, _, r in tight if r['C_same_p'] >= r['Delta_p'] - 1e-9)
    pd_n = sum(1 for _, _, r in tight if r['C_same_n'] >= r['Delta_n'] - 1e-9)
    print(f"  per-domain  C_same_+ >= Delta_+ : {pd_p}/{len(tight)};  "
          f"C_same_- >= Delta_- : {pd_n}/{len(tight)}")
    # global closure: (C_same_+ - Delta_+) + (C_same_- - Delta_-) >= C_hard  <=>  Q <= 0
    glob = sum(1 for _, _, r in tight
               if (r['C_same_p'] - r['Delta_p']) + (r['C_same_n'] - r['Delta_n'])
               >= r['C_hard'] - 1e-7)
    print(f"  global  (Cs+ - D+)+(Cs- - D-) >= C_hard : {glob}/{len(tight)}  (== Q<=0)")
    # which domain carries the deficit? per-domain surplus s_dom = C_same_dom - Delta_dom
    worst = min(tight, key=lambda x: min(x[2]['C_same_p'] - x[2]['Delta_p'],
                                         x[2]['C_same_n'] - x[2]['Delta_n']))
    fn, nm, r = worst
    print(f"\n  most negative per-domain surplus: {nm}")
    print(f"    Delta_+={r['Delta_p']:.3f} C_same_+={r['C_same_p']:.3f} "
          f"(surplus {r['C_same_p']-r['Delta_p']:+.3f})")
    print(f"    Delta_-={r['Delta_n']:.3f} C_same_-={r['C_same_n']:.3f} "
          f"(surplus {r['C_same_n']-r['Delta_n']:+.3f})")
    print(f"    C_hard={r['C_hard']:.3f}  Q={r['Q']:.3e}")
    print("=" * 96)


if __name__ == "__main__":
    main()
