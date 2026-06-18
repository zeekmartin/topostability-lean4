"""
Exact nodal-domain decomposition of the aggregate triangle-Poincare surplus

    Surplus  Q := T - lam2 * fDf
             T   = sum_{ab in E} t_ab (f_a - f_b)^2     (per-edge triangle energy)
             fDf = sum_v d_v f_v^2                       (= degQuad)
             t_ab = |N(a) cap N(b)|  = (A^2)_ab on edges  (triangles on edge ab)

Goal: find an EXACT identity in which the negative reservoir appears GLOBALLY
(not edge-wise), using the eigen-equation  sum_{u~v}(f_v - f_u) = lam2 f_v.

MASTER IDENTITY (derived, exact when L f = lam2 f):

    T - lam2*fDf  =  sum_v (tau_v - lam2 d_v) f_v^2   -   2 sum_{ab in E} t_ab f_a f_b
                  =  Delta                            -   C
       tau_v = sum_{u~v} t_{vu}   (= twice #triangles through v)
       Delta = sum_v (tau_v - lam2 d_v) f_v^2                  ("diagonal")
       C     = 2 sum_{ab in E} t_ab f_a f_b                    ("triangle correlation")

Sign split of the correlation by nodal class (V+ = {f>=0}, V- = {f<0}):
       C = C_same - C_hard
       C_same = 2 sum_{same-sign edges} t_ab |f_a f_b|   >= 0   (global reservoir)
       C_hard = 2 sum_{cross-sign  edges} t_ab |f_a f_b|  >= 0   (hard positive mass)

  =>   Q = Delta + C_hard - C_same.
       aggregate Poincare  Q <= 0   <=>   Delta + C_hard <= C_same.

This is the reduction: the negative reservoir is the GLOBAL same-sign triangle
correlation C_same; the obstruction is the diagonal Delta plus the global hard
cross-correlation C_hard.

Also tests classical nodal identities (Dirichlet split, per-domain eigen-balance)
and fL^2f = lam2^2 as sanity checks, on the 536-graph corpus + targeted hard families.

Run: python conjecture_B_nodal_decomposition.py
"""
import numpy as np
import networkx as nx


# ------------------------------------------------------------------ core quantities
def graph_data(G):
    """Return a dict of all spectral / triangle quantities for the unit Fiedler vector."""
    nodes = list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal()
    A = np.diag(d) - L
    ev, V = np.linalg.eigh(L)
    lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])      # unit-norm Fiedler vector
    A2 = A @ A                                  # (A^2)_ab = common neighbours
    n = len(nodes)

    # per-edge triangle weight t_ab (only on edges), and edge list with signs
    T = 0.0
    C = 0.0                                     # 2 sum t_ab f_a f_b
    C_same = 0.0
    C_hard = 0.0
    D_pp = D_mm = D_cross = 0.0                 # nodal Dirichlet split (unweighted)
    T_pp = T_mm = T_cross = 0.0                 # nodal triangle-energy split
    Bd_p = Bd_m = 0.0                           # eigen-boundary terms
    Tbd_p = Tbd_m = 0.0                         # triangle-weighted boundary terms
    Vpos = f >= 0.0

    iu = np.triu(A, 1)
    ea, eb = np.nonzero(iu)
    for ia, ib in zip(ea.tolist(), eb.tolist()):
        t = A2[ia, ib]
        fa, fb = f[ia], f[ib]
        g2 = (fa - fb) ** 2
        T += t * g2
        C += 2.0 * t * fa * fb
        same = (fa >= 0) == (fb >= 0)
        if same:
            C_same += 2.0 * t * abs(fa * fb)
            if Vpos[ia]:
                D_pp += g2; T_pp += t * g2
            else:
                D_mm += g2; T_mm += t * g2
        else:
            C_hard += 2.0 * t * abs(fa * fb)
            D_cross += g2; T_cross += t * g2
            # boundary eigen / triangle terms (V+ endpoint vs V- endpoint)
            if Vpos[ia]:           # ia in V+, ib in V-
                Bd_p += fa * (fa - fb);   Bd_m += fb * (fb - fa)
                Tbd_p += t * fa * (fa - fb);  Tbd_m += t * fb * (fb - fa)
            else:                  # ia in V-, ib in V+
                Bd_m += fa * (fa - fb);   Bd_p += fb * (fb - fa)
                Tbd_m += t * fa * (fa - fb);  Tbd_p += t * fb * (fb - fa)

    tau = (A2 * A).sum(axis=1)                  # tau_v = sum_{u~v} t_{vu}
    fDf = float((d * f * f).sum())
    Delta = float(((tau - lam * d) * f * f).sum())
    Mpos = float((f[Vpos] ** 2).sum())
    Mneg = float((f[~Vpos] ** 2).sum())
    L2 = L @ L
    fL2f = float(f @ L2 @ f)

    return dict(n=n, m=len(ea), lam=lam, f=f, d=d,
                T=T, fDf=fDf, Q=T - lam * fDf,
                Delta=Delta, C=C, C_same=C_same, C_hard=C_hard,
                D_pp=D_pp, D_mm=D_mm, D_cross=D_cross,
                T_pp=T_pp, T_mm=T_mm, T_cross=T_cross,
                Bd_p=Bd_p, Bd_m=Bd_m, Tbd_p=Tbd_p, Tbd_m=Tbd_m,
                Mpos=Mpos, Mneg=Mneg, fL2f=fL2f, sumf=float(f.sum()),
                degLin=float((d * f).sum()))


# ------------------------------------------------------------------ graph families
def deg2dense(n, q, s):
    r = np.random.default_rng(s)
    G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for bb in r.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(bb))
    return G


def degk(n, q, k, s):
    r = np.random.default_rng(s)
    G = nx.gnp_random_graph(n - 1, q, seed=int(r.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for bb in r.choice(range(1, n), size=min(k, n - 1), replace=False):
        G.add_edge(0, int(bb))
    return G


def chain_cliques(m, k):
    G = nx.complete_graph(m)
    for c in range(1, k):
        H = nx.relabel_nodes(nx.complete_graph(m), {i: i + c * m for i in range(m)})
        G = nx.union(G, H); G.add_edge((c - 1) * m, c * m)
    return G


def corpus():
    out = []
    rng = np.random.default_rng(13)
    for _ in range(150):
        out.append(("gnp", nx.gnp_random_graph(int(rng.integers(8, 24)),
                    float(rng.uniform(0.3, 0.7)), seed=int(rng.integers(0, 2**31)))))
    for _ in range(150):
        out.append(("deg2dense", deg2dense(int(rng.integers(20, 80)),
                    float(rng.uniform(0.4, 0.8)), int(rng.integers(0, 2**31)))))
    for _ in range(100):
        out.append(("degk", degk(int(rng.integers(20, 80)), float(rng.uniform(0.4, 0.8)),
                    int(rng.integers(1, 5)), int(rng.integers(0, 2**31)))))
    for _ in range(80):
        out.append(("lollipop", nx.lollipop_graph(int(rng.integers(8, 40)),
                    int(rng.integers(3, 18)))))
    for _ in range(60):
        out.append(("watts", nx.watts_strogatz_graph(int(rng.integers(15, 30)), 4, 0.3,
                    seed=int(rng.integers(0, 2**31)))))
    # ---- targeted HARD families (bottlenecks / glued cliques) ----
    for m in (10, 20, 50):
        for L in (3, 5, 10):
            out.append(("lollipop_hard", nx.lollipop_graph(m, L)))
        for L in (3, 5):
            out.append(("barbell", nx.barbell_graph(m, L)))
    for m, k in ((10, 2), (10, 3), (20, 2), (20, 3), (15, 4), (30, 2)):
        out.append(("chain_cliques", chain_cliques(m, k)))
    for m, p in ((40, 0.5), (60, 0.5), (73, 0.75)):     # dense (worst-case style)
        out.append(("dense_gnp", nx.gnp_random_graph(m, p, seed=m)))
    return out


# ------------------------------------------------------------------ main
def main():
    graphs = corpus()
    res_master = []     # |Q - (Delta - C)|
    res_split  = []     # |Q - (Delta + C_hard - C_same)|
    res_corr   = []     # |C - (C_same - C_hard)|
    res_dir     = []    # |D_pp+D_mm+D_cross - lam|   (unit norm -> Dirichlet = lam)
    res_vplus   = []    # |D_pp + Bd_p - lam*Mpos|
    res_vminus  = []    # |D_mm + Bd_m - lam*Mneg|
    res_L2      = []    # |fL2f - lam^2|
    res_tbd     = []    # |T_cross - (Tbd_p + Tbd_m)|

    ratios = []         # (Delta + C_hard) / C_same          -- want <= 1
    delta_le_csame = [] # Delta / C_same
    delta_sign = []     # Delta itself
    Q_holds = 0
    reduction_holds = 0
    n_ok = 0
    by_family = {}
    worst = (-1e9, None)

    for fam, G in graphs:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        try:
            r = graph_data(G)
        except Exception:
            continue
        if r['lam'] < 1e-9:
            continue
        n_ok += 1

        res_master.append(abs(r['Q'] - (r['Delta'] - r['C'])))
        res_split.append(abs(r['Q'] - (r['Delta'] + r['C_hard'] - r['C_same'])))
        res_corr.append(abs(r['C'] - (r['C_same'] - r['C_hard'])))
        res_dir.append(abs(r['D_pp'] + r['D_mm'] + r['D_cross'] - r['lam']))
        res_vplus.append(abs(r['D_pp'] + r['Bd_p'] - r['lam'] * r['Mpos']))
        res_vminus.append(abs(r['D_mm'] + r['Bd_m'] - r['lam'] * r['Mneg']))
        res_L2.append(abs(r['fL2f'] - r['lam'] ** 2))
        res_tbd.append(abs(r['T_cross'] - (r['Tbd_p'] + r['Tbd_m'])))

        if r['Q'] <= 1e-9:
            Q_holds += 1
        obstruction = r['Delta'] + r['C_hard']
        if obstruction <= r['C_same'] + 1e-9:
            reduction_holds += 1
        if r['C_same'] > 1e-12:
            ratio = obstruction / r['C_same']
            ratios.append(ratio)
            delta_le_csame.append(r['Delta'] / r['C_same'])
            if ratio > worst[0]:
                worst = (ratio, (fam, r['n'], r['m'], r['lam'], r['Delta'],
                                 r['C_hard'], r['C_same'], r['Q']))
        delta_sign.append(r['Delta'])
        by_family.setdefault(fam, []).append(obstruction / r['C_same'] if r['C_same'] > 1e-12 else 0.0)

    def line(name, arr, fmt="{:.2e}"):
        a = np.array([x for x in arr if np.isfinite(x)])
        if not len(a):
            print(f"  {name}: (none)"); return
        print(f"  {name}: max={fmt.format(a.max())} median={fmt.format(np.median(a))} "
              f"mean={fmt.format(a.mean())}")

    print("=" * 74)
    print(f"graphs analysed: {n_ok}")
    print("\n--- EXACT IDENTITY RESIDUALS (want ~1e-12, machine zero) ---")
    line("Q = Delta - C                         ", res_master)
    line("Q = Delta + C_hard - C_same           ", res_split)
    line("C = C_same - C_hard                   ", res_corr)
    line("Dirichlet  D++ +D-- +Dx = lam         ", res_dir)
    line("V+ balance  D++ +Bd+ = lam*M+         ", res_vplus)
    line("V- balance  D-- +Bd- = lam*M-         ", res_vminus)
    line("fL^2f = lam^2                          ", res_L2)
    line("T_cross = Tbd+ + Tbd-                  ", res_tbd)

    print("\n--- REDUCTION:  Q<=0  <=>  Delta + C_hard <= C_same ---")
    rr = np.array(ratios)
    print(f"  Q <= 0 holds:                        {Q_holds}/{n_ok}")
    print(f"  reduction (D+C_hard <= C_same) holds: {reduction_holds}/{n_ok}")
    print(f"  (Delta+C_hard)/C_same : max={rr.max():.4f} median={np.median(rr):.4f} "
          f"mean={rr.mean():.4f}")
    ds = np.array(delta_le_csame)
    print(f"  Delta/C_same          : max={ds.max():.4f} median={np.median(ds):.4f} "
          f"min={ds.min():.4f}")
    dsg = np.array(delta_sign)
    print(f"  Delta sign            : frac(Delta<=0)={np.mean(dsg <= 1e-12):.3f} "
          f"max={dsg.max():.4e} min={dsg.min():.4e}")
    if worst[1]:
        fam, n, m, lam, De, Ch, Cs, Q = worst[1]
        print(f"  WORST ratio={worst[0]:.4f}: {fam} n={n} m={m} lam={lam:.3f} "
              f"Delta={De:.4f} C_hard={Ch:.4f} C_same={Cs:.4f} Q={Q:.4e}")

    print("\n--- reduction ratio by family (max (D+C_hard)/C_same) ---")
    for fam in sorted(by_family):
        a = np.array(by_family[fam])
        print(f"  {fam:16s} n={len(a):3d}  max={a.max():.3f}  median={np.median(a):.3f}")
    print("=" * 74)


if __name__ == "__main__":
    main()
