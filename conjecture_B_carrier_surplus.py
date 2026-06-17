"""
Carrier-vertex surplus generalization.
Carriers H = {v : f_v² ≥ 1/n}.  surplus_c = λ₂ mass_c - energy_c (per apex).
CSurplus(v) = Σ_{c∈N(v)} surplus_c = (A·surplus)_v.   β(v) = CSurplus(v)/f_v².
Deficit = λ₂ fᵀDf - T = Σ_c surplus_c ;  Required = λ₂(λ₂ + S²/m - fᵀDf).
Run:  python conjecture_B_carrier_surplus.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce
from conjecture_B_apex_surplus import apex, deg2dense


def carrier_data(G):
    r = apex(G)
    n = r["n"]; f2 = r["f2"]; A = r["A"]; sp = r["surplus"]
    CS = A @ sp                                   # CSurplus(v) = Σ_{c~v} surplus_c
    H = np.flatnonzero(f2 >= 1.0 / n)             # carriers
    d = r["d"]; l2 = r["l2"]
    # edges in G[N(v)] and max triangle count on edges at v
    nbrs = [np.flatnonzero(A[v] > 0.5) for v in range(n)]
    A2 = A @ A
    out = []
    for v in H:
        Nv = nbrs[v]
        nbhd_edges = float(A[np.ix_(Nv, Nv)].sum() / 2) if len(Nv) else 0.0
        # t_max on edges incident to v
        tmax = 0.0
        for c in Nv:
            tmax = max(tmax, float(A2[v, c]))
        out.append(dict(v=int(v), dv=int(d[v]), fv2=float(f2[v]),
                        CS=float(CS[v]), beta=float(CS[v] / f2[v]) if f2[v] > 0 else 0.0,
                        nbhd_edges=nbhd_edges, tmax=tmax))
    Deficit = float(sp.sum()); S = r["S"]; m = r["m"]; fDf = r["fDf"]
    Required = l2 * (l2 + S * S / m - fDf)
    return dict(n=n, l2=l2, Deficit=Deficit, Required=Required,
                carriers=out, H_CS=float(CS[H].sum()))


def corpus(maxn=9):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        Tg = ce.triangle_graph(G)
        if Tg.number_of_nodes() < 2 or not nx.is_connected(Tg):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=3))
        if key not in seen:
            seen[key] = G.copy()
    return list(seen.values())


def beta_profile(allc, label):
    print(f"  [{label}] β by carrier degree d_v:")
    bydeg = {}
    for c in allc:
        bydeg.setdefault(c["dv"], []).append(c["beta"])
    for dv in sorted(bydeg):
        b = np.array(bydeg[dv])
        if len(b) >= 1:
            print(f"     d_v={dv:3d} (n={len(b):4d}): β min={b.min():+.3f} med={np.median(b):+.3f} "
                  f"max={b.max():+.3f}  neg(β<0):{int((b<0).sum())}")


def main():
    # ---------- TASK 1: β by degree on various families ----------
    print("===== TASK 1: β(v)=CSurplus(v)/f_v² profiled by degree =====")
    # deg2+dense
    allc = []
    for n in (50, 100, 200, 500):
        G = deg2dense(n, 0.65, seed=300 + n)
        if nx.is_connected(G):
            allc += carrier_data(G)["carriers"]
    beta_profile(allc, "deg2+dense n=50..500")
    # corpus
    cc = []
    for G in corpus(9):
        cc += carrier_data(G)["carriers"]
    beta_profile(cc, "corpus n≤9")
    # ER
    ec = []
    for p in (0.1, 0.3, 0.5):
        G = nx.gnp_random_graph(50, p, seed=7)
        if nx.is_connected(G):
            ec += carrier_data(G)["carriers"]
    beta_profile(ec, "ER n=50 p=.1,.3,.5")
    # WS
    wc = []
    for k in (4, 8):
        for p in (0.1, 0.3):
            G = nx.watts_strogatz_graph(50, k, p, seed=7)
            if nx.is_connected(G):
                wc += carrier_data(G)["carriers"]
    beta_profile(wc, "WS n=50 k=4,8 p=.1,.3")
    # named
    nc = []
    for name, G in [("Petersen", nx.petersen_graph()),
                    ("K_{3,5}", nx.complete_bipartite_graph(3, 5)),
                    ("K_{4,4}", nx.complete_bipartite_graph(4, 4)),
                    ("C_20", nx.cycle_graph(20))]:
        if nx.is_connected(G) and nx.is_connected(ce.triangle_graph(G)):
            nc += carrier_data(G)["carriers"]
    beta_profile(nc, "Petersen/K_{m,n}/C20")

    # ---------- TASK 2: carrier fraction of Deficit ----------
    print("\n===== TASK 2: carrier_fraction = Σ_H CSurplus / Deficit =====")
    for n in (50, 100, 200, 500):
        G = deg2dense(n, 0.65, seed=300 + n)
        if not nx.is_connected(G):
            continue
        r = carrier_data(G)
        cf = r["H_CS"] / r["Deficit"] if abs(r["Deficit"]) > 1e-9 else float("nan")
        print(f"  deg2+dense n={n}: Deficit={r['Deficit']:.3f} Required={r['Required']:.3f} "
              f"(B:{r['Deficit']>=r['Required']-1e-9})  Σ_H CSurplus={r['H_CS']:.3f}  "
              f"carrier_fraction={cf:.3f}  #carriers={len(r['carriers'])}")

    # ---------- TASK 3: what determines β ----------
    print("\n===== TASK 3: candidate β formulas (pooled carriers) =====")
    pool = allc + cc + ec + wc + nc
    bv = np.array([c["beta"] for c in pool]); dv = np.array([c["dv"] for c in pool], float)
    # we need λ₂ per carrier — recompute alongside (store)? approximate via corr only
    print(f"  pooled carriers: {len(pool)}; β: min={bv.min():+.3f} med={np.median(bv):.3f} "
          f"max={bv.max():+.3f}  neg:{int((bv<0).sum())}")
    print(f"  corr(β, d_v)={np.corrcoef(bv,dv)[0,1]:+.3f}")
    # test β ≈ λ₂  (need λ₂); recompute per family below in TASK 3b
    # candidate: β vs d_v scatter (median β per degree)
    for dvtest in (1, 2, 3, 4, 5, 6):
        m = dv == dvtest
        if m.sum():
            print(f"     d_v={dvtest}: median β={np.median(bv[m]):+.3f} (n={int(m.sum())})  "
                  f"[β≈λ₂? β≈λ₂-(d_v-1)? β≈λ₂/d_v?]")

    # TASK 3b: relate β to λ₂ explicitly on deg2+dense and small graphs
    print("  β vs λ₂ on graphs with a dominant carrier:")
    for n in (100, 200, 500):
        G = deg2dense(n, 0.65, seed=300 + n)
        if not nx.is_connected(G):
            continue
        r = carrier_data(G)
        dom = max(r["carriers"], key=lambda c: c["fv2"])
        print(f"    deg2+dense n={n}: λ₂={r['l2']:.3f}, dominant carrier d_v={dom['dv']} "
              f"f_v²={dom['fv2']:.3f} β={dom['beta']:.3f}  (β/λ₂={dom['beta']/r['l2']:.3f}, "
              f"β vs 2(λ₂-1)={2*(r['l2']-1):.3f})")

    # ---------- TASK 4: spread-Fiedler families ----------
    print("\n===== TASK 4: spread-Fiedler families — is Required ≤ 0 (B trivial)? =====")
    fams = [("3-regular(petersen)", nx.petersen_graph()),
            ("4-regular C_50^2", nx.circulant_graph(50, [1, 2])),
            ("ER n=50 p=.3", nx.gnp_random_graph(50, 0.3, seed=1)),
            ("ER n=50 p=.5", nx.gnp_random_graph(50, 0.5, seed=1)),
            ("K_{4,4}", nx.complete_bipartite_graph(4, 4)),
            ("K_{5,5}", nx.complete_bipartite_graph(5, 5)),
            ("WS n=50 k=8 p=.3", nx.watts_strogatz_graph(50, 8, 0.3, seed=1))]
    for name, G in fams:
        if not nx.is_connected(G):
            continue
        Tg = ce.triangle_graph(G)
        tconn = (Tg.number_of_nodes() >= 2 and nx.is_connected(Tg))
        r = carrier_data(G)
        reg = "regular" if len(set(dict(G.degree()).values())) == 1 else "irregular"
        print(f"  {name:22s} ({reg}, Tconn={tconn}): Deficit={r['Deficit']:.3f} "
              f"Required={r['Required']:+.3f} "
              f"{'(Required≤0 ⇒ B trivial, carrier moot)' if r['Required']<=1e-9 else '(Required>0!)'}")


if __name__ == "__main__":
    main()
