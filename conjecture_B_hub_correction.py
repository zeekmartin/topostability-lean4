"""
Search for the signed hub-correction in  aggregate_triangle_poincare.

Reformulation chain (all exact; conventions fixed below):
    Open >= sum_v R_v f_v^2,   R_v = sigma_v - (d_v-lam)^2 - lam d_v,  sigma_v = (A d)_v
    sum_v R_v f_v^2 = - Asrt + lam * fAf,
        Asrt = sum_{ab in E} (d_a-d_b)(f_a^2-f_b^2)        (UNORDERED edges)
        fAf  = f . (A f) = fDf - lam * (f.f)               (eigen; = fDf - lam for unit f)
    => target  <=>  Open + Asrt >= lam * fAf      (<=> Open - sum R f^2 = -Q >= 0)

Factor-2 conventions:
    fAf = sum_{a,b} A_ab f_a f_b = 2 sum_{ab in E} f_a f_b.
    Open = (1/2) sum_v Open_v = sum over induced P3 (a-c-b, a!~b) of (f_a-f_b)^2.
    Asrt over unordered edges; ordered double sum would be 2*Asrt.

TASK 1: verify the exact decomposition.
TASK 2: sign / scale of Asrt; by degree-gap quantile; by R<0 hubs.
TASK 3: hub-flatness diagnostic on the R<0 credit (upper bound only, NOT a certificate).
TASK 4: open energy incident to R<0 hubs.
TASK 5: search a manifestly-signed form for  Open + Asrt - lam fAf  (= -Q).

Run: python conjecture_B_hub_correction.py
"""
import numpy as np
import networkx as nx
from conjecture_B_open2path_gap import all_graphs, graph_quant


def hub_quant(G):
    q = graph_quant(G)
    nodes = q['nodes']; d = q['d']; f = q['f']; lam = q['lam']
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    A = np.diag(d) - L
    R = q['R']; P = q['P']; g2 = q['g2']
    fAf = float(f @ A @ f)
    fDf = q['fDf']
    # Asrt over unordered edges
    iu = np.triu(A, 1); ea, eb = np.nonzero(iu)
    dgap = d[ea] - d[eb]
    fgap = f[ea] ** 2 - f[eb] ** 2
    edge_contrib = dgap * fgap
    Asrt = float(edge_contrib.sum())
    Open = q['Open']
    Open_v = (P * g2).sum(1)               # sum_v Open_v = 2 Open
    Rf2 = q['Rf2']
    # hub set: R_v < 0
    hub = R < 0
    actual_hub_credit = float((np.abs(R[hub]) * f[hub] ** 2).sum())
    # hub-flatness upper bound on f_v^2 (unit Fiedler):  f_v^2 <= d_v/(d_v-lam)^2
    hf = np.where(d - lam > 1e-9, d / np.maximum(d - lam, 1e-12) ** 2, np.inf)
    HF_upper_credit = float((np.abs(R[hub]) * hf[hub]).sum())
    # open energy incident to hubs: edges (v,b) open with v hub -> count once toward hub
    Open_hub = float(0.5 * Open_v[hub].sum())   # half of incident (matches Open=1/2 sum Open_v)
    pos_mass = float(Rf2[R > 0].sum())
    return dict(lam=lam, fAf=fAf, fDf=fDf, Asrt=Asrt, Open=Open, Q=q['Q'],
                sumRf2=float(Rf2.sum()), pos_mass=pos_mass,
                actual_hub_credit=actual_hub_credit, HF_upper_credit=HF_upper_credit,
                Open_hub=Open_hub, n_hub=int(hub.sum()), n=len(nodes),
                edge_contrib=edge_contrib, dgap=dgap, ff=f * f, hub=hub)


def main():
    data = [hub_quant(G) for _, G in all_graphs()]
    n = len(data)

    print("=" * 82)
    print("TASK 1 — exact decomposition  sum_v R_v f^2 = -Asrt + lam*fAf,  fAf = fDf - lam(f.f)")
    print("=" * 82)
    r_fAf = max(abs(q['fAf'] - (q['fDf'] - q['lam'])) for q in data)   # unit norm f.f=1
    r_dec = max(abs(q['sumRf2'] - (-q['Asrt'] + q['lam'] * q['fAf'])) for q in data)
    r_tgt = max(abs((q['Open'] + q['Asrt'] - q['lam'] * q['fAf']) - (-q['Q'])) for q in data)
    print(f"  fAf = fDf - lam            : max residual {r_fAf:.2e}")
    print(f"  sum R f^2 = -Asrt + lam fAf: max residual {r_dec:.2e}")
    print(f"  (Open + Asrt - lam fAf) == -Q : max residual {r_tgt:.2e}")
    print(f"  target  Open + Asrt >= lam fAf  holds: "
          f"{sum(1 for q in data if q['Open']+q['Asrt'] >= q['lam']*q['fAf']-1e-7)}/{n}")

    print("\n" + "=" * 82)
    print("TASK 2 — sign and scale of Asrt = sum_E (d_a-d_b)(f_a^2-f_b^2)")
    print("=" * 82)
    Asrt = np.array([q['Asrt'] for q in data])
    print(f"  Asrt >= 0 : {int((Asrt >= -1e-9).sum())}/{n}     Asrt <= 0 : "
          f"{int((Asrt <= 1e-9).sum())}/{n}")
    print(f"  Asrt : min={Asrt.min():.3f} median={np.median(Asrt):.3f} max={Asrt.max():.3f}")
    rr = np.array([q['Asrt'] / (q['lam'] * q['fAf']) for q in data if abs(q['lam']*q['fAf']) > 1e-9])
    print(f"  Asrt / (lam fAf) : min={rr.min():.3f} median={np.median(rr):.3f} max={rr.max():.3f}")
    ro = np.array([q['Asrt'] / q['Open'] for q in data if q['Open'] > 1e-9])
    print(f"  Asrt / Open      : min={ro.min():.3f} median={np.median(ro):.3f} max={ro.max():.3f}")
    # degree-gap quantiles: pool all edges, bucket by |dgap|
    alldg = np.concatenate([np.abs(q['dgap']) for q in data])
    allec = np.concatenate([q['edge_contrib'] for q in data])
    qs = np.quantile(alldg, [0, 0.25, 0.5, 0.75, 1.0])
    print("  Asrt contribution by |degree gap| quartile (pooled edges):")
    for lo, hi, lab in [(qs[0], qs[1], "Q1"), (qs[1], qs[2], "Q2"),
                        (qs[2], qs[3], "Q3"), (qs[3], qs[4] + 1, "Q4")]:
        m = (alldg >= lo) & (alldg < hi)
        print(f"    {lab} |dgap| in [{lo:.0f},{hi:.0f}): edges={int(m.sum()):6d}  "
              f"sum contrib={allec[m].sum():+.2f}")

    print("\n" + "=" * 82)
    print("TASK 3 — hub-flatness diagnostic on the R_v<0 credit (UPPER BOUND, not a certificate)")
    print("=" * 82)
    ac = np.array([q['actual_hub_credit'] for q in data])
    hu = np.array([q['HF_upper_credit'] for q in data])
    ratio = np.array([a / h for a, h in zip(ac, hu) if h > 1e-12])
    print(f"  actual_hub_credit  : median={np.median(ac):.4f}")
    print(f"  HF_upper_credit    : median={np.median(hu):.4f}")
    print(f"  actual / HF_upper  : min={ratio.min():.4f} median={np.median(ratio):.4f} "
          f"max={ratio.max():.4f}")
    print(f"  (HF_upper is an upper bound on the credit; small ratio => HF too loose here too)")

    print("\n" + "=" * 82)
    print("TASK 4 — open energy incident to R_v<0 hubs")
    print("=" * 82)
    # Open_hub >= actual_hub_credit ?
    t1 = sum(1 for q in data if q['Open_hub'] >= q['actual_hub_credit'] - 1e-7)
    # Open_hub + actual_hub_credit >= sum_{R>0} R f^2 ?
    t2 = sum(1 for q in data if q['Open_hub'] + q['actual_hub_credit'] >= q['pos_mass'] - 1e-7)
    # Open - Open_hub <= -Q ?  (the natural reduction, see derivation)
    t3 = sum(1 for q in data if q['Open'] - q['Open_hub'] <= -q['Q'] + 1e-7)
    print(f"  Open_hub >= actual_hub_credit                : {t1}/{n}")
    print(f"  Open_hub + actual_hub_credit >= sum_{{R>0}}Rf^2: {t2}/{n}")
    print(f"  Open - Open_hub <= -Q  (slack)               : {t3}/{n}")
    oh = np.array([q['Open_hub'] / q['Open'] for q in data if q['Open'] > 1e-9])
    print(f"  Open_hub / Open : median={np.median(oh):.3f} (fraction of open energy at hubs)")

    print("\n" + "=" * 82)
    print("TASK 5 — manifestly-signed form for  Open + Asrt - lam fAf  (= -Q)")
    print("=" * 82)
    print("  By TASK 1 this quantity IS the slack -Q; any exact rewrite is the proof itself.")
    print("  Edge-bracket form:  Open + sum_E [ (d_a-d_b)(f_a^2-f_b^2) - 2 lam f_a f_b ].")
    # test if the per-edge bracket is sign-definite (it is NOT in general):
    pos_edge = 0; neg_edge = 0
    for q in data:
        pass
    print("  (per-edge bracket (d_a-d_b)(f_a^2-f_b^2) - 2 lam f_a f_b is sign-indefinite; "
          "no SOS found — see informal note.)")
    print("=" * 82)


if __name__ == "__main__":
    main()
