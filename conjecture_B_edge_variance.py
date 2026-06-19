"""
Edge-variance form of Conjecture B (Scenario 2), with the factor fixed.

Per edge e={a,b}:  h_e = f_a+f_b (lift),  g_e = f_a-f_b (gradient),  t_e = #common nbrs.
  Sum g^2 = f^T L f = lam2 ;  Sum h^2 = f^T Q f = 2fDf - lam2 ;  S = Sum h_e = Sum d_v f_v.
  T = Sum_e t_e g_e^2 = f^T L_M f (triangle energy).
  G := Sum h^2 - S^2/m = Sum_e (h_e - hbar)^2 = m * Var_E(h)  (hbar = S/m).

CORRECTED CONJECTURE (det round: det(M_low)=(4 lam2/n)(lam2 G_det - m T), G_det = m fQf - S^2 = m G):
   B  <=>  lam2 G_det >= m T  <=>  T <= lam2 G.    (NO extra m on T; "mT<=lam2 G" was off by m.)

TASK1 per-edge t_e g_e^2 vs (h_e - hbar)^2.
TASK2 weighted vs unweighted; T<=lam2^2 ? G>=lam2 ?
TASK3 the variance G vs lam2.
TASK4 Cauchy-Schwarz on edge pairs.
TASK5 regular-graph proof (CLEAN): t_e<=d-1, T<=(d-1)lam2 <= lam2(2d-lam2)=lam2 G.
Run: python conjecture_B_edge_variance.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def edge_data(G):
    nodes = list(G.nodes()); n = len(nodes); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    m = G.number_of_edges()
    w, U = np.linalg.eigh(L); lam = w[1]; f = U[:, 1].copy()
    A2 = A @ A
    es = [(idx[a], idx[b]) for a, b in G.edges()]
    t = np.array([A2[a, b] for a, b in es])           # common neighbours
    ge = np.array([f[a] - f[b] for a, b in es])
    he = np.array([f[a] + f[b] for a, b in es])
    fab = np.array([f[a] * f[b] for a, b in es])
    fDf = float(d @ (f * f)); S = float(d @ f)
    g2 = ge ** 2; h2 = he ** 2
    T = float((t * g2).sum())
    G = float(h2.sum() - S ** 2 / m)
    return dict(n=n, m=m, lam=lam, d=d, f=f, t=t, ge=ge, he=he, g2=g2, h2=h2, fab=fab,
                fDf=fDf, S=S, T=T, G=G, hbar=S / m, A=A)


def all_graphs():
    gs = [("corpus", G) for _, G in corpus()]
    gs += [("barbell", nx.barbell_graph(mm, Lb)) for mm in (5, 20, 40, 80) for Lb in (0, 1, 3)]
    gs += [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (40, 40), (3, 60))]
    gs += [("chain", chain_cliques(mm, k)) for mm, k in ((10, 2), (20, 2), (40, 2), (15, 4))]
    out = []
    for fam, G in gs:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        ev = np.linalg.eigvalsh(nx.laplacian_matrix(G, nodelist=list(G.nodes()))
                                .toarray().astype(float))
        if ev[1] < 1e-9:
            continue
        out.append((fam, G))
    return out


def main():
    data = [edge_data(G) for _, G in all_graphs()]
    ng = len(data); tol = 1e-7

    print("=" * 74)
    print("FACTOR CORRECTION: B <=> T <= lam2 G  (NOT mT <= lam2 G)")
    print("=" * 74)
    okT = sum(1 for q in data if q['T'] <= q['lam'] * q['G'] + tol)
    okMT = sum(1 for q in data if q['m'] * q['T'] <= q['lam'] * q['G'] + tol)
    ratios = np.array([q['T'] / (q['lam'] * q['G']) for q in data if q['lam'] * q['G'] > 1e-12])
    print(f"  T <= lam2 G   (correct)      : {okT}/{ng}  (T/(lam2 G) max={ratios.max():.4f})")
    print(f"  mT <= lam2 G  (as stated)    : {okMT}/{ng}  (off by factor m -> fails)")
    # sanity: Sum g^2 = lam2, Sum h^2 = 2fDf-lam2, Sum h_e = S
    r1 = max(abs(q['g2'].sum() - q['lam']) for q in data)
    r2 = max(abs(q['h2'].sum() - (2 * q['fDf'] - q['lam'])) for q in data)
    r3 = max(abs(q['he'].sum() - q['S']) for q in data)
    print(f"  sanity: Sum g^2=lam2 ({r1:.1e}); Sum h^2=2fDf-lam2 ({r2:.1e}); Sum h_e=S ({r3:.1e})")

    # ---------------- TASK 1 ----------------
    print("\n" + "=" * 74)
    print("TASK 1 — per-edge t_e g_e^2 vs (h_e - hbar)^2")
    print("=" * 74)
    corrs = []; peredge_ok = 0; peredge_tot = 0; Cmax = []
    for q in data:
        x = q['t'] * q['g2']
        y = (q['he'] - q['hbar']) ** 2
        if x.std() > 1e-12 and y.std() > 1e-12:
            corrs.append(np.corrcoef(x, y)[0, 1])
        # per-edge t_e g_e^2 <= lam2 (h_e-hbar)^2 ?
        ok = x <= q['lam'] * y + 1e-9
        peredge_ok += int(ok.sum()); peredge_tot += len(x)
        mask = y > 1e-12
        if mask.any():
            Cmax.append(float((x[mask] / y[mask]).max()))
    print(f"  corr(t_e g_e^2, (h_e-hbar)^2) pooled-per-graph mean = {np.mean(corrs):+.3f}")
    print(f"  per-edge t_e g_e^2 <= lam2 (h_e-hbar)^2 : {peredge_ok}/{peredge_tot} "
          f"({100*peredge_ok/peredge_tot:.1f}%)")
    print(f"  universal C with t_e g_e^2 <= C (h_e-hbar)^2: needs C >= max ratio = "
          f"{max(Cmax):.1f} (vs lam2 median {np.median([q['lam'] for q in data]):.2f}) -> per-edge FAILS")

    # ---------------- TASK 2 ----------------
    print("\n" + "=" * 74)
    print("TASK 2 — sufficient conditions  T <= lam2^2  and  G >= lam2")
    print("=" * 74)
    okT2 = sum(1 for q in data if q['T'] <= q['lam'] ** 2 + tol)
    print(f"  T <= lam2^2 : {okT2}/{ng}  (would suffice if G>=lam2; usually FALSE: T~(D-1)lam2)")
    # T <= (Delta-1) lam2 (rigorous: t_e<=Delta-1)
    okTd = sum(1 for q in data if q['T'] <= (q['d'].max() - 1) * q['lam'] + 1e-7)
    print(f"  T <= (Delta-1) lam2 (rigorous t_e<=Delta-1): {okTd}/{ng}")
    # anti-correlation t vs g^2
    ac = [np.corrcoef(q['t'], q['g2'])[0, 1] for q in data
          if q['t'].std() > 1e-12 and q['g2'].std() > 1e-12]
    print(f"  corr(t_e, g_e^2) (anti-correlation): mean={np.mean(ac):+.3f}")

    # ---------------- TASK 3 ----------------
    print("\n" + "=" * 74)
    print("TASK 3 — variance G vs lam2")
    print("=" * 74)
    rG = np.array([q['G'] / q['lam'] for q in data])
    geG = sum(1 for q in data if q['G'] >= q['lam'] - tol)
    print(f"  G/lam2 : min={rG.min():.3f} median={np.median(rG):.2f} max={rG.max():.2f}")
    print(f"  G >= lam2 : {geG}/{ng}")
    # combined sufficient: T<=lam2^2 AND G>=lam2
    comb = sum(1 for q in data if q['T'] <= q['lam']**2 + tol and q['G'] >= q['lam'] - tol)
    print(f"  (T<=lam2^2 AND G>=lam2) [sufficient]: {comb}/{ng}")

    # ---------------- TASK 4 ----------------
    print("\n" + "=" * 74)
    print("TASK 4 — Cauchy-Schwarz on edge pairs")
    print("=" * 74)
    # T = Sum t_e g^2; G = Sum (h_e-hbar)^2.  Try CS: T = Sum (sqrt(t_e) g_e)(sqrt(t_e) g_e) ...
    # Test the natural CS:  T = Sum t_e g_e^2 <= sqrt(Sum t_e^2 g_e^2 ... ) -- not obviously tied to G.
    # Instead test the *bound that works on regular*: T <= (max_e t_e) lam2 and compare to lam2 G.
    okmaxt = sum(1 for q in data if q['t'].max() * q['lam'] <= q['lam'] * q['G'] + tol)
    print(f"  T <= (max_e t_e) lam2 <= lam2 G ? (max_t <= G): {okmaxt}/{ng}")
    geGt = sum(1 for q in data if q['G'] >= q['t'].max() - tol)
    print(f"  G >= max_e t_e : {geGt}/{ng}  (clean sufficient: then T<=max_t*lam2<=lam2 G)")

    # ---------------- TASK 5 ----------------
    print("\n" + "=" * 74)
    print("TASK 5 — regular-graph proof (CLEAN)")
    print("=" * 74)
    regs = {"C20": nx.cycle_graph(20), "K8": nx.complete_graph(8),
            "Petersen": nx.petersen_graph(), "Q4": nx.hypercube_graph(4),
            "circ(13,{1,5})": nx.circulant_graph(13, [1, 5]),
            "K33": nx.complete_bipartite_graph(3, 3)}
    print(f"  {'graph':16s} {'d':>3} {'lam2':>7} {'G':>9} {'2d-lam2':>9} {'T':>9} "
          f"{'(d-1)lam2':>10} {'lam2 G':>10} {'B?':>3}")
    for name, Gr in regs.items():
        q = edge_data(Gr)
        d0 = q['d'][0]
        regular = np.allclose(q['d'], d0)
        lam = q['lam']; G = q['G']; T = q['T']
        bound = (d0 - 1) * lam
        ok = T <= lam * G + 1e-7
        print(f"  {name:16s} {int(d0):3d} {lam:7.3f} {G:9.3f} {2*d0-lam:9.3f} {T:9.3f} "
              f"{bound:10.3f} {lam*G:10.3f} {'Y' if ok else 'N':>3}"
              + ("" if regular else "  (NOT regular)"))
    print("  CLEAN PROOF (regular d): S=0 => G=Sum h^2=fQf=2d-lam2; t_e<=d-1 =>")
    print("    T=Sum t_e g^2 <= (d-1) Sum g^2 = (d-1)lam2 <= (2d-lam2)lam2 = lam2 G")
    print("    [since 2d-lam2 >= d-1 <=> lam2 <= d+1, always].  => B for regular graphs. QED")

    print("\n" + "=" * 74)
    print("SUMMARY")
    print("=" * 74)
    print(f"  Corrected: B <=> T <= lam2 G (T/(lam2 G) max {ratios.max():.3f}).")
    print(f"  Per-edge t_e g^2 <= lam2 (h_e-hbar)^2 FAILS ({100*peredge_ok/peredge_tot:.0f}%); "
          f"G>=max_e t_e on {geGt}/{ng} (clean sufficient where it holds).")
    print("  REGULAR graphs: clean proof T<=(d-1)lam2<=lam2 G via t_e<=d-1.")


if __name__ == "__main__":
    main()
