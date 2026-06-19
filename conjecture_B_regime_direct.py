"""
Direct T <= RHS per regime, WITHOUT aggregate Poincare.

RHS = lam2(f^TQf - S^2/m) = lam2(2fDf - lam2 - S^2/m).  B (lift) <=> T <= RHS.
Required = lam2(lam2 + S^2/m - fDf);  regime (i) Required<=0  <=> fAf=fDf-lam2 >= S^2/m.

KEY exact identity (analytic):
   A2_diag := sum_v[sigma_v-(d_v-lam2)^2]f_v^2 = T + Open = 2 lam2 fDf - lam2^2 - A   (A=Cov_L(d,f^2))
   RHS = 2 lam2 fDf - lam2^2 - lam2 S^2/m
   => A2_diag - RHS = lam2 S^2/m - A.
So A2_diag <= RHS  <=>  A >= lam2 S^2/m   (the TASK-3 hypothesis).

TASK1 margins in regime (i): margin_direct=(RHS-T)/RHS vs margin_AP=(lam2 fDf - T)/(lam2 fDf).
TASK2/3 does A2_diag <= RHS hold (esp. in regime i)? If yes, T<=T+Open<=RHS closes B w/o AP.
TASK4 regime (ii) TYPE A (vertex bottleneck): T/RHS.
TASK5 regime (ii) TYPE B (path bottleneck): T = O(lam2^2), RHS=Theta(lam2), T/RHS->0.
TASK6 coverage.
Run: python conjecture_B_regime_direct.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(fam, G):
    nodes = list(G.nodes()); n = len(nodes); idx = {u: i for i, u in enumerate(nodes)}
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L
    m = G.number_of_edges()
    w, U = np.linalg.eigh(L); lam = w[1]; f = U[:, 1].copy()
    f2 = f * f
    A2 = A @ A; Mtri = A * A2; P = A2 - np.diag(d) - Mtri
    L_M = np.diag(Mtri.sum(1)) - Mtri; L_P = np.diag(P.sum(1)) - P
    T = float(f @ L_M @ f); Open = float(f @ L_P @ f)
    fDf = float(d @ f2); S = float(d @ f)
    Acal = float(sum((d[idx[a]] - d[idx[b]]) * (f2[idx[a]] - f2[idx[b]]) for a, b in G.edges()))
    S2m = S * S / m
    RHS = lam * (2 * fDf - lam - S2m)
    Required = lam * (lam + S2m - fDf)
    A2_diag = T + Open
    return dict(fam=fam, n=n, m=m, lam=lam, T=T, Open=Open, A2_diag=A2_diag, fDf=fDf, S=S,
                S2m=S2m, RHS=RHS, Required=Required, Acal=Acal, APrhs=lam * fDf)


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
    data = [graph_quant(fam, G) for fam, G in all_graphs()]
    ng = len(data); tol = 1e-7

    # sanity: exact identities
    r_id = max(abs((q['A2_diag'] - q['RHS']) - (q['lam'] * q['S2m'] - q['Acal'])) for q in data)
    # lift slack RHS - T = Open + A - lam2 S^2/m  (cf -Q = Open + A - lam2 fAf)
    r_slack = max(abs((q['RHS'] - q['T']) - (q['Open'] + q['Acal'] - q['lam'] * q['S2m']))
                  for q in data)
    # RHS - T = -Q - Required   (-Q = lam2 fDf - T is the AP slack)
    r_q = max(abs((q['RHS'] - q['T']) - ((q['lam'] * q['fDf'] - q['T']) - q['Required']))
              for q in data)
    print(f"EXACT: A2_diag - RHS == lam2 S^2/m - Cov_L(d,f^2)  : residual {r_id:.2e}")
    print(f"EXACT: RHS - T == Open + Cov_L(d,f^2) - lam2 S^2/m : residual {r_slack:.2e}")
    print(f"EXACT: RHS - T == (-Q) - Required  (AP slack - Required) : residual {r_q:.2e}\n")

    reg_i = [q for q in data if q['Required'] <= tol]
    reg_ii = [q for q in data if q['Required'] > tol]
    print(f"regime (i)  Required<=0 : {len(reg_i)}/{ng}")
    print(f"regime (ii) Required>0  : {len(reg_ii)}/{ng}\n")

    # ---------------- TASK 1 ----------------
    print("=" * 74)
    print("TASK 1 — margins in regime (i): direct (RHS) vs aggregate-Poincare (lam2 fDf)")
    print("=" * 74)
    md = np.array([(q['RHS'] - q['T']) / q['RHS'] for q in reg_i if q['RHS'] > 1e-12])
    ma = np.array([(q['APrhs'] - q['T']) / q['APrhs'] for q in reg_i if q['APrhs'] > 1e-12])
    print(f"  margin_direct=(RHS-T)/RHS    : min={md.min():.4f} median={np.median(md):.3f}")
    print(f"  margin_AP=(lam2 fDf-T)/(lam2 fDf): min={ma.min():.4f} median={np.median(ma):.3f}")
    tightest = min(reg_i, key=lambda q: q['T'] / q['RHS'] if q['RHS'] > 1e-12 else 9)
    print(f"  TIGHTEST T/RHS in regime (i): {tightest['T']/tightest['RHS']:.4f} "
          f"(fam={tightest['fam']} n={tightest['n']} lam={tightest['lam']:.3f})")

    # ---------------- TASK 2/3 ----------------
    print("\n" + "=" * 74)
    print("TASK 2/3 — does A2_diag <= RHS (would close B via T<=T+Open<=RHS)?")
    print("=" * 74)
    a2_all = sum(1 for q in data if q['A2_diag'] <= q['RHS'] + tol)
    a2_regi = sum(1 for q in reg_i if q['A2_diag'] <= q['RHS'] + tol)
    print(f"  A2_diag <= RHS  (all graphs)        : {a2_all}/{ng}")
    print(f"  A2_diag <= RHS  (regime i only)     : {a2_regi}/{len(reg_i)}")
    print(f"  <=>  Cov_L(d,f^2) >= lam2 S^2/m     : same counts (exact identity above)")
    # by how much does it fail? Open vs the slack (RHS - T)
    over = np.array([(q['A2_diag'] - q['RHS']) for q in reg_i])
    print(f"  A2_diag - RHS in regime (i): min={over.min():.3f} median={np.median(over):.3f} "
          f"max={over.max():.3f}")
    # the failure amount = Open - (RHS - T) = Open - slack
    print(f"  => A2_diag-RHS = lam2 S^2/m - A; A=Cov_L mostly <0 so A2_diag>RHS. Open is NOT slack.")
    fail_open = np.array([q['Open'] / (q['RHS'] - q['T']) for q in reg_i
                          if q['RHS'] - q['T'] > 1e-9])
    print(f"  Open / (RHS - T) in regime (i): median={np.median(fail_open):.2f} "
          f"(Open >> lift slack => can't discard Open)")

    # ---------------- TASK 4/5 ----------------
    print("\n" + "=" * 74)
    print("TASK 4/5 — regime (ii): T/RHS by family (TYPE A vertex vs TYPE B path bottleneck)")
    print("=" * 74)
    from collections import defaultdict
    byfam = defaultdict(list)
    for q in reg_ii:
        byfam[q['fam']].append(q['T'] / q['RHS'] if q['RHS'] > 1e-12 else np.nan)
    for fam, vals in sorted(byfam.items()):
        vals = np.array([v for v in vals if np.isfinite(v)])
        if len(vals):
            print(f"  {fam:10s}: n={len(vals):4d}  T/RHS min={vals.min():.4f} "
                  f"median={np.median(vals):.4f} max={vals.max():.4f}")
    # T/RHS scaling vs lam2 (TYPE B: T=O(lam2^2), RHS=Theta(lam2) => T/RHS ~ lam2 -> 0 for small lam2)
    print("  (small-lam2 bottleneck graphs => T/RHS small; large T/RHS = dense regime-ii)")

    # ---------------- TASK 6 ----------------
    print("\n" + "=" * 74)
    print("TASK 6 — coverage")
    print("=" * 74)
    b_all = sum(1 for q in data if q['T'] <= q['RHS'] + tol)
    print(f"  B = T <= RHS holds : {b_all}/{ng}")
    print(f"  regime (i) closed by A2_diag<=RHS (no AP) : {a2_regi}/{len(reg_i)}  -> "
          f"{'FALSE, AP still needed' if a2_regi < len(reg_i) else 'YES'}")
    # within regime (i), is T<=RHS (B) always true even though A2_diag<=RHS fails? (yes, that's B)
    bi = sum(1 for q in reg_i if q['T'] <= q['RHS'] + tol)
    print(f"  regime (i): B (T<=RHS) holds {bi}/{len(reg_i)} (via AP T<=lam2 fDf<=RHS)")
    bii = sum(1 for q in reg_ii if q['T'] <= q['RHS'] + tol)
    print(f"  regime (ii): B (T<=RHS) holds {bii}/{len(reg_ii)}")

    print("\n" + "=" * 74)
    print("CONCLUSION")
    print("=" * 74)
    print(f"  TASK 3 HYPOTHESIS FALSE: A2_diag<=RHS only {a2_all}/{ng} (regime i: {a2_regi}/{len(reg_i)}).")
    print("  A2_diag - RHS = lam2 S^2/m - Cov_L(d,f^2); Cov_L mostly negative => A2_diag > RHS.")
    print("  Open is LOAD-BEARING (not discardable slack); regime (i) still needs aggregate Poincare")
    print("  (T <= lam2 fDf), which is the open lemma. The 3-way bypass does NOT eliminate it.")


if __name__ == "__main__":
    main()
