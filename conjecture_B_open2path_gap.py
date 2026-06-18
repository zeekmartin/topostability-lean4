"""
The diagonal-vs-open-energy inequality for aggregate_triangle_poincare.

Exact identity (verified earlier, formalised pieces in Lean):
    T + Open = sum_v [sigma_v - (d_v - lam)^2] f_v^2 ,      T = f^T L_M f >= 0,  Open = f^T L_P f >= 0
with sigma_v = sum_{c~v} d_c = (A d)_v.  Aggregate Poincare  T <= lam sum_v d_v f_v^2  is equivalent to

    Open >= sum_v R_v f_v^2 ,     R_v = sigma_v - (d_v - lam)^2 - lam d_v
                                       = (sigma_v - d_v^2) + lam (d_v - lam).

Open 2-path Laplacian L_P = diag(p) - P,  P_ab = (A^2)_ab [a not~ b, a != b],  p_v = sigma_v - d_v - tau_v.
Open energy:  Open = (1/2) sum_v Open_v,  Open_v = sum_b P_vb (f_v - f_b)^2.
Equivalently  Open = sum over induced P3 (a - c - b, a not~ b) of (f_a - f_b)^2.

TASK 1: sign structure of R_v.
TASK 2: localize Open vs R_v.
TASK 3: candidate inequalities  Open_v >= R_v^+ f_v^2  (local / aggregated over sets S).
TASK 4: spectral Rayleigh  Open / sum_{R>0} R_v f_v^2.
TASK 5: exact identity for  Open - sum_v R_v f_v^2.

Run: python conjecture_B_open2path_gap.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(G):
    nodes = list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    diagd = np.diag(d)
    M = A * A2
    P = A2 - diagd - M
    sigma = A @ d
    tau = M.sum(1)
    pdeg = P.sum(1)                          # open-2-path degree = sigma - d - tau
    R = sigma - (d - lam) ** 2 - lam * d     # R_v
    R_alt = (sigma - d ** 2) + lam * (d - lam)
    L_M = np.diag(tau) - M
    L_P = np.diag(pdeg) - P
    T = float(f @ L_M @ f)
    Open = float(f @ L_P @ f)
    fDf = float((d * f * f).sum())
    g2 = np.subtract.outer(f, f) ** 2
    Open_v = (P * g2).sum(1)                 # sum_b P_vb (f_v-f_b)^2 ; sum_v Open_v = 2 Open
    Rf2 = R * f * f
    return dict(nodes=nodes, lam=lam, d=d, f=f, sigma=sigma, tau=tau, pdeg=pdeg,
                R=R, R_alt=R_alt, T=T, Open=Open, fDf=fDf, Open_v=Open_v, Rf2=Rf2,
                Q=T - lam * fDf, P=P, g2=g2)


def all_graphs():
    gs = [("corpus", G) for _, G in corpus()]
    gs += [("barbell", nx.barbell_graph(m, Lb)) for m in (5, 20, 40, 80) for Lb in (0, 1, 3)]
    gs += [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (40, 40), (3, 60))]
    gs += [("chain", chain_cliques(m, k)) for m, k in ((10, 2), (20, 2), (40, 2), (15, 4))]
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
    data = [(fam, graph_quant(G)) for fam, G in all_graphs()]
    n_graphs = len(data)

    # ---------------- TASK 5 first: exact identities ----------------
    print("=" * 80)
    print("TASK 5 — exact identities")
    print("=" * 80)
    r_alt = max(np.max(np.abs(q['R'] - q['R_alt'])) for _, q in data)
    # Open - sum R f^2 == -Q
    r_circ = max(abs((q['Open'] - q['Rf2'].sum()) - (-q['Q'])) for _, q in data)
    # Open == (1/2) sum_v Open_v
    r_half = max(abs(q['Open'] - 0.5 * q['Open_v'].sum()) for _, q in data)
    print(f"  R_v = (sigma-d^2) + lam(d-lam)             : max residual {r_alt:.2e}")
    print(f"  Open - sum_v R_v f_v^2  ==  -Q (slack)     : max residual {r_circ:.2e}")
    print(f"  Open == (1/2) sum_v Open_v                 : max residual {r_half:.2e}")
    print("  => 'Open - sum R f^2' IS the slack -Q (circular); not a new sign-exposing identity.")

    # ---------------- TASK 1: sign of R_v ----------------
    print("\n" + "=" * 80)
    print("TASK 1 — sign structure of R_v")
    print("=" * 80)
    frac_pos = []; pos_mass = []; neg_mass = []
    corr_deg = []; corr_tau = []; corr_open = []; corr_f2 = []
    for _, q in data:
        R, f, d, tau, pdeg = q['R'], q['f'], q['d'], q['tau'], q['pdeg']
        frac_pos.append(np.mean(R > 1e-9))
        Rf2 = q['Rf2']
        pos_mass.append(Rf2[R > 0].sum())
        neg_mass.append(Rf2[R <= 0].sum())
        if R.std() > 1e-9:
            corr_deg.append(np.corrcoef(R, d)[0, 1])
            corr_tau.append(np.corrcoef(R, tau)[0, 1])
            corr_open.append(np.corrcoef(R, pdeg)[0, 1])
            corr_f2.append(np.corrcoef(R, f ** 2)[0, 1])
    frac_pos = np.array(frac_pos)
    print(f"  fraction of vertices with R_v > 0 : min={frac_pos.min():.3f} "
          f"median={np.median(frac_pos):.3f} max={frac_pos.max():.3f}")
    print(f"  graphs with ALL R_v > 0           : {int((frac_pos > 0.999).sum())}/{n_graphs}")
    pm = np.array(pos_mass); nm = np.array(neg_mass)
    print(f"  sum_{{R>0}} R f^2  : median={np.median(pm):.4f}")
    print(f"  sum_{{R<=0}} R f^2 : median={np.median(nm):.4f}  (negative mass helps the bound)")
    print(f"  total sum R f^2 = (T+Open) - lam fDf : median="
          f"{np.median([q['Rf2'].sum() for _, q in data]):.4f}")
    print(f"  corr(R_v, .): degree={np.nanmean(corr_deg):+.2f}  tau={np.nanmean(corr_tau):+.2f}  "
          f"open-deg={np.nanmean(corr_open):+.2f}  f^2={np.nanmean(corr_f2):+.2f}")

    # ---------------- TASK 2: localize Open ----------------
    print("\n" + "=" * 80)
    print("TASK 2 — localization of Open vs R_v>0 vertices")
    print("=" * 80)
    conc = []
    for _, q in data:
        R, Ov = q['R'], q['Open_v']
        tot = Ov.sum()
        if tot > 1e-12:
            conc.append(Ov[R > 0].sum() / tot)
    conc = np.array(conc)
    print(f"  fraction of total Open_v carried by R_v>0 vertices: "
          f"median={np.median(conc):.3f} min={conc.min():.3f}")

    # ---------------- TASK 3: candidate inequalities ----------------
    print("\n" + "=" * 80)
    print("TASK 3 — candidate inequalities")
    print("=" * 80)
    # local: (1/2) Open_v >= R_v^+ f_v^2 ?   (1/2 because sum_v Open_v = 2 Open)
    loc_ok = 0; loc_tot = 0
    for _, q in data:
        R, Ov, f = q['R'], q['Open_v'], q['f']
        Rp = np.maximum(R, 0.0) * f * f
        loc = 0.5 * Ov >= Rp - 1e-9
        loc_ok += int(loc.sum()); loc_tot += len(R)
    print(f"  LOCAL  (1/2)Open_v >= R_v^+ f_v^2 : holds at {loc_ok}/{loc_tot} vertices "
          f"({100*loc_ok/loc_tot:.1f}%)")

    # aggregated over sets S
    def agg_test(setfn, label):
        ok = 0
        for _, q in data:
            R, Ov, f = q['R'], q['Open_v'], q['f']
            S = setfn(q)
            lhs = 0.5 * Ov[S].sum()
            rhs = (np.maximum(R, 0.0) * f * f)[S].sum()
            if lhs >= rhs - 1e-7:
                ok += 1
        print(f"  AGG over {label:22s}: (1/2)sum_S Open_v >= sum_S R^+ f^2 : {ok}/{n_graphs}")

    agg_test(lambda q: q['f'] >= 0, "nodal V+")
    agg_test(lambda q: q['f'] < 0, "nodal V-")
    agg_test(lambda q: q['R'] > 0, "high-R (R>0)")
    agg_test(lambda q: q['d'] >= np.median(q['d']), "high-degree half")
    agg_test(lambda q: q['f'] ** 2 >= np.median(q['f'] ** 2), "high-|f| half")
    agg_test(lambda q: np.ones(len(q['R']), bool), "ALL (== aggregate Q<=0)")

    # ---------------- TASK 4: spectral Rayleigh ----------------
    print("\n" + "=" * 80)
    print("TASK 4 — spectral Rayleigh  Open / sum_{R>0} R f^2")
    print("=" * 80)
    ray = []
    for _, q in data:
        R, f = q['R'], q['f']
        denom = (np.maximum(R, 0.0) * f * f).sum()
        if denom > 1e-12:
            ray.append(q['Open'] / denom)
    ray = np.array(ray)
    print(f"  Open / sum_{{R>0}} R f^2 : min={ray.min():.4f} median={np.median(ray):.3f} "
          f"max={ray.max():.3f}")
    print(f"  >= 1 (Open dominates positive-R mass alone): {int((ray >= 1 - 1e-9).sum())}/{len(ray)}")
    # the true inequality uses ALL R (incl. negative), so compare:
    ray_all = []
    for _, q in data:
        denom = q['Rf2'].sum()
        if abs(denom) > 1e-12:
            ray_all.append(q['Open'] / denom if denom > 0 else np.inf)
    ray_all = np.array([r for r in ray_all if np.isfinite(r)])
    print(f"  Open / sum_ALL R f^2 (denom>0): min={ray_all.min():.4f} "
          f"median={np.median(ray_all):.3f}  (>=1 == Q<=0)")
    print("=" * 80)


if __name__ == "__main__":
    main()
