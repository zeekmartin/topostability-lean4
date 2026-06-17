"""
Positive/negative apex-surplus decomposition.
surplus_c = λ₂·mass_c − energy_c,  mass_c=Σ_{v∈N(c)}f_v²,  energy_c=E_{G[N(c)]}(f).
Deficit = Σ_c surplus_c = λ₂fᵀDf − T ;  Required = λ₂(λ₂+S²/m−fᵀDf) ;  B ⟺ Deficit≥Required.
Run:  python conjecture_B_apex_surplus.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def apex(G):
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    fDf = float((d * f * f).sum()); S = float(d @ f)
    Required = l2 * (l2 + S * S / m - fDf)
    f2 = f * f
    mass = np.zeros(n); energy = np.zeros(n); dens = np.zeros(n)
    nbrs = [np.flatnonzero(A[c] > 0.5) for c in range(n)]
    for c in range(n):
        Nc = nbrs[c]
        if len(Nc) == 0:
            continue
        fc = f[Nc]; Asub = A[np.ix_(Nc, Nc)]
        degsub = Asub.sum(1)
        mass[c] = f2[Nc].sum()
        energy[c] = float((degsub * fc * fc).sum() - fc @ Asub @ fc)
        ne = degsub.sum() / 2.0
        dens[c] = ne / max(len(Nc) * (len(Nc) - 1) / 2.0, 1.0)
    surplus = l2 * mass - energy
    return dict(n=n, l2=l2, fDf=fDf, S=S, m=m, Required=Required, d=d, f=f, f2=f2,
                mass=mass, energy=energy, surplus=surplus, dens=dens, A=A,
                Deficit=float(surplus.sum()))


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


def main():
    print("===== TASK 1: surplus by degree quartile (deg2+dense) =====")
    for n in (50, 100, 200, 500, 1000):
        G = deg2dense(n, 0.65, seed=300 + n)
        if not nx.is_connected(G):
            continue
        r = apex(G); d = r["d"]; sp = r["surplus"]
        qs = np.quantile(d, [0.25, 0.5, 0.75])
        print(f"  n={n}: Deficit={r['Deficit']:.3f} Required={r['Required']:.3f} "
              f"pos/neg surplus = {sp[sp>0].sum():.3f}/{(-sp[sp<0].sum()):.3f}")
        for lab, lo, hi in [("Q1", -1, qs[0]), ("Q2", qs[0], qs[1]),
                            ("Q3", qs[1], qs[2]), ("Q4", qs[2], 1e9)]:
            mask = (d > lo) & (d <= hi)
            if mask.sum():
                print(f"     {lab} (d∈({lo:.0f},{hi:.0f}], {int(mask.sum())} apices): "
                      f"Σsurplus={sp[mask].sum():+.3f}  (+:{int((sp[mask]>0).sum())} "
                      f"−:{int((sp[mask]<0).sum())})")

    print("\n===== TASK 2: can low-degree apices alone close B? =====")
    for n in (50, 100, 200, 500, 1000):
        G = deg2dense(n, 0.65, seed=300 + n)
        if not nx.is_connected(G):
            continue
        r = apex(G); d = r["d"]; sp = r["surplus"]
        med = np.median(d)
        low = sp[d <= med].sum(); high = sp[d > med].sum()
        print(f"  n={n}: low_surplus(d≤med)={low:.3f}  high_surplus={high:+.3f}  "
              f"Required={r['Required']:.3f}  low≥Req: {low >= r['Required']-1e-9}")

    print("\n===== TASK 3: closing thresholds (Good-set definitions) =====")
    G = deg2dense(500, 0.65, seed=300 + 500); r = apex(G)
    d = r["d"]; sp = r["surplus"]; Req = r["Required"]; f2 = r["f2"]; dens = r["dens"]
    print(f"  (deg2+dense n=500, Required={Req:.3f}, Deficit={r['Deficit']:.3f})")
    # (a) Good = {d_c ≤ k}: smallest degree-quantile threshold
    print("  (a) Good={d_c≤k}:  Σ_Good surplus  vs  Required+|Σ_Bad⁻|")
    for qfrac in (0.1, 0.25, 0.5, 0.75, 1.0):
        k = np.quantile(d, qfrac)
        good = d <= k
        sg = sp[good].sum(); badneg = -sp[~good][sp[~good] < 0].sum()
        ok = sg >= Req + badneg - 1e-9
        print(f"     q={qfrac}: k={k:.0f}, Σ_Good={sg:+.3f}, |Σ_Bad⁻|={badneg:.3f}, "
              f"close: {ok}")
    # (c) Good = {f_c² ≤ thr}: hub-flatness informed (low Fiedler mass on apex)
    print("  (c) Good={f_c²≤thr} (apex has small Fiedler value):")
    for tf in (0.5, 0.9, 0.99):
        thr = np.quantile(f2, tf)
        good = f2 <= thr
        sg = sp[good].sum(); badneg = -sp[~good][sp[~good] < 0].sum()
        print(f"     thr=q{tf}({thr:.4f}): Σ_Good={sg:+.3f}, close: {sg >= Req+badneg-1e-9}")
    # (b) Good = {density(G[N(c)]) ≤ ρ}
    print("  (b) Good={density(G[N(c)])≤ρ}:")
    for rho in (0.3, 0.5, 0.7, 1.0):
        good = dens <= rho
        sg = sp[good].sum(); badneg = -sp[~good][sp[~good] < 0].sum()
        print(f"     ρ={rho}: {int(good.sum())} apices, Σ_Good={sg:+.3f}, "
              f"close: {sg >= Req+badneg-1e-9}")

    print("\n===== TASK 4: WHY low-degree apices have surplus =====")
    for n in (200, 500):
        G = deg2dense(n, 0.65, seed=300 + n); r = apex(G)
        d = r["d"]; sp = r["surplus"]; f2 = r["f2"]; A = r["A"]
        # vertex 0 (degree 2) and its neighbours
        adj0 = np.flatnonzero(A[0] > 0.5)
        order = np.argsort(-sp)
        print(f"  n={n}: vertex0 deg={int(d[0])}, f_0²={f2[0]:.4f}, surplus_0={sp[0]:.4f}")
        print(f"     neighbours of vertex0: {adj0.tolist()}, their surplus="
              f"{[round(float(sp[a]),3) for a in adj0]}, mass={[round(float(r['mass'][a]),3) for a in adj0]}")
        print(f"     top-3 surplus apices (idx,deg,surplus,mass,energy):")
        for c in order[:3]:
            print(f"        c={c} d={int(d[c])} surplus={sp[c]:.3f} mass={r['mass'][c]:.3f} "
                  f"energy={r['energy'][c]:.3f} f_c²={f2[c]:.4f} (nbr of 0: {bool(A[0,c]>0.5)})")
        # dense apex (high degree, not nbr of 0): is energy_c ≈ λ₂ mass_c?
        densei = [c for c in range(n) if d[c] >= np.median(d) and A[0, c] < 0.5][:1]
        for c in densei:
            print(f"     dense apex c={c} d={int(d[c])}: surplus={sp[c]:.4f} "
                  f"energy/(λ₂·mass)={r['energy'][c]/(r['l2']*r['mass'][c]+1e-12):.3f} (Poincaré tightness)")

    print("\n===== TASK 5: candidate per-apex epsilon (energy_c ≤ (1-ε)λ₂ mass_c) =====")
    # ε_c = 1 - energy_c/(λ₂ mass_c) ; report distribution by degree class
    for n in (200, 500):
        G = deg2dense(n, 0.65, seed=300 + n); r = apex(G)
        d = r["d"]; eps = 1 - r["energy"] / (r["l2"] * r["mass"] + 1e-15)
        med = np.median(d)
        nbr0 = np.flatnonzero(r["A"][0] > 0.5)
        is_nbr0 = np.zeros(n, bool); is_nbr0[nbr0] = True
        print(f"  n={n}: ε_c = 1 - energy_c/(λ₂ mass_c):")
        print(f"     nbrs-of-0 apices: ε mean={eps[is_nbr0].mean():.3f} (these carry surplus)")
        print(f"     other low (d≤med): ε mean={eps[(d<=med)&~is_nbr0].mean():.3f}")
        print(f"     dense (d>med): ε mean={eps[d>med].mean():.3f} min={eps[d>med].min():.3f} "
              f"(<0 = local Poincaré fails)")


if __name__ == "__main__":
    main()
