"""
Spectral neighborhood bounds for the apex energy. T = Σ_c E_{G[N(c)]}(f).
Per apex c: energy_c = fᵀL_{H_c}f ≤ λ_max(L_{H_c})·var_c (Rayleigh, mean-centred).
Compare to Poincaré λ₂(G)·mass_c. Test aggregates and hybrid vs RHS = λ₂(fᵀQf - S²/m).
Run:  python conjecture_B_spectral_neighborhood.py
"""
import numpy as np
import networkx as nx
import counterexample_search as ce


def analyse(G):
    if not nx.is_connected(G):
        return None
    nodes = list(G.nodes()); n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy(); A = np.diag(d) - L; m = int(G.number_of_edges())
    ev, V = np.linalg.eigh(L); l2 = float(ev[1]); f = V[:, 1] / np.linalg.norm(V[:, 1])
    if l2 < 1e-9:
        return None
    fDf = float((d * f * f).sum()); S = float(d @ f)
    RHS = l2 * (2 * fDf - l2 - S * S / m)
    f2 = f * f
    rows = []
    for c in range(n):
        Nc = np.flatnonzero(A[c] > 0.5)
        dc = len(Nc)
        if dc == 0:
            continue
        fc = f[Nc]; Asub = A[np.ix_(Nc, Nc)]; degsub = Asub.sum(1)
        LH = np.diag(degsub) - Asub
        energy = float((degsub * fc * fc).sum() - fc @ Asub @ fc)
        mass = float((fc * fc).sum())
        mean = float(fc.mean()); var = float(((fc - mean) ** 2).sum())
        lam_max = float(np.linalg.eigvalsh(LH)[-1]) if dc >= 1 else 0.0
        dens = float(degsub.sum() / 2 / max(dc * (dc - 1) / 2, 1))
        rows.append((energy, mass, var, lam_max, dc, dens))
    R = np.array(rows)  # energy, mass, var, lam_max, dc, dens
    return dict(n=n, l2=l2, RHS=RHS, T=float(R[:, 0].sum()), R=R, fDf=fDf)


def corpus(maxn=9, cap=400):
    seen = {}
    for tag, exh, G in ce._gen_graphs_hier(maxn):
        if G.number_of_nodes() < 3 or not nx.is_connected(G):
            continue
        Tg = ce.triangle_graph(G)
        if Tg.number_of_nodes() < 2 or not nx.is_connected(Tg):
            continue
        key = (G.number_of_nodes(), G.number_of_edges(),
               nx.weisfeiler_lehman_graph_hash(G, iterations=2))
        if key not in seen:
            seen[key] = G.copy()
        if len(seen) >= cap:
            break
    return list(seen.values())


def deg2dense(n, q, seed):
    rng = np.random.default_rng(seed)
    G = nx.gnp_random_graph(n - 1, q, seed=int(rng.integers(0, 2**31)))
    G = nx.relabel_nodes(G, {i: i + 1 for i in range(n - 1)}); G.add_node(0)
    for b in rng.choice(range(1, n), size=2, replace=False):
        G.add_edge(0, int(b))
    return G


def families():
    fams = [("corpus", G) for G in corpus(9)]
    for n in (50, 100):
        fams.append(("deg2dense", deg2dense(n, 0.65, 300 + n)))
    for m in (20, 50):
        fams += [("lollipop", nx.lollipop_graph(m, 5)), ("lollipop", nx.lollipop_graph(m, 10)),
                 ("barbell", nx.barbell_graph(m, 3))]
    fams += [("circulant", nx.circulant_graph(40, [1, 2])),
             ("circulant", nx.circulant_graph(50, [1, 2, 3])),
             ("ER", nx.gnp_random_graph(50, 0.3, seed=1)),
             ("ER", nx.gnp_random_graph(50, 0.5, seed=2)),
             ("WS", nx.watts_strogatz_graph(50, 8, 0.3, seed=1))]
    # multi-bottleneck chain
    G = nx.complete_graph(15)
    for c in range(1, 3):
        H = nx.relabel_nodes(nx.complete_graph(15), {i: i + c * 15 for i in range(15)})
        G = nx.union(G, H); G.add_edge((c - 1) * 15, c * 15)
    fams.append(("chain", G))
    return fams


def main():
    data = []
    for lab, G in families():
        r = analyse(G)
        if r:
            r["label"] = lab; data.append(r)
    print(f"graphs: {len(data)}")

    # ---- TASK 1: local bound violations ----
    print("\n===== TASK 1: per-apex local-bound violations (pooled) =====")
    tot = 0; va = vb = vc = vd = 0
    for r in data:
        R = r["R"]; l2 = r["l2"]
        e, mass, var, lmax, dc, dens = R[:, 0], R[:, 1], R[:, 2], R[:, 3], R[:, 4], R[:, 5]
        tot += len(R)
        va += int(np.sum(e > lmax * var + 1e-7))                 # (a) Rayleigh (should be 0)
        vb += int(np.sum(e > l2 * mass + 1e-7))                  # (b) local Poincaré
        vc += int(np.sum(e > l2 * var + 1e-7))                   # (c) λ₂·var
        vd += int(np.sum(e > dens * dc * var + 1e-7))            # (d) density·d·var
    print(f"  apices: {tot}")
    print(f"  (a) energy ≤ λ_max·var : viol {va} (Rayleigh, expect 0)")
    print(f"  (b) energy ≤ λ₂·mass   : viol {vb} ({100*vb/tot:.1f}%) [local Poincaré]")
    print(f"  (c) energy ≤ λ₂·var    : viol {vc} ({100*vc/tot:.1f}%)")
    print(f"  (d) energy ≤ dens·d·var: viol {vd} ({100*vd/tot:.1f}%)")

    # ---- TASK 2 + 4: aggregates vs RHS ----
    print("\n===== TASK 2/4: aggregate bounds vs RHS (per family, max ratio) =====")
    print(f"{'family':11s} {'#':>3} {'Σλmax·var/RHS':>14} {'Σλ₂·var/RHS':>12} "
          f"{'Σλ₂·mass/RHS':>13} {'hybrid/RHS':>11} {'T/RHS':>7}")
    fam_order = ["corpus", "deg2dense", "lollipop", "barbell", "chain",
                 "circulant", "ER", "WS"]
    worst_hybrid = (None, 0.0)
    for lab in fam_order:
        g = [r for r in data if r["label"] == lab]
        if not g:
            continue
        def ratios(r):
            R = r["R"]; l2 = r["l2"]; RHS = r["RHS"]
            e, mass, var, lmax = R[:, 0], R[:, 1], R[:, 2], R[:, 3]
            a1 = (lmax * var).sum() / RHS
            a2 = l2 * var.sum() / RHS
            a3 = l2 * mass.sum() / RHS
            hyb = np.minimum(lmax * var, l2 * mass).sum() / RHS
            return a1, a2, a3, hyb, r["T"] / RHS
        rs = [ratios(r) for r in g]
        mx = lambda k: max(x[k] for x in rs)
        print(f"{lab:11s} {len(g):3d} {mx(0):14.3f} {mx(1):12.3f} {mx(2):13.3f} "
              f"{mx(3):11.3f} {mx(4):7.3f}")
        for r, x in zip(g, rs):
            if x[3] > worst_hybrid[1]:
                worst_hybrid = (r, x[3])
    # overall hybrid closure
    nclose = 0; tot_g = 0
    for r in data:
        R = r["R"]; l2 = r["l2"]; RHS = r["RHS"]
        hyb = np.minimum(R[:, 3] * R[:, 2], l2 * R[:, 1]).sum()
        tot_g += 1
        if hyb <= RHS + 1e-7:
            nclose += 1
    print(f"\n  HYBRID T_hybrid = Σ min(λ_max·var, λ₂·mass) ≤ RHS : {nclose}/{tot_g}")
    if worst_hybrid[0]:
        wr = worst_hybrid[0]
        print(f"  worst hybrid/RHS = {worst_hybrid[1]:.3f} on {wr['label']} n={wr['n']}")

    # ---- TASK 3: dense-apex spectral structure (deg2dense, circulant) ----
    print("\n===== TASK 3: does λ_max·var beat λ₂·mass on dense apices? =====")
    for lab in ("deg2dense", "circulant"):
        g = [r for r in data if r["label"] == lab]
        for r in g[:1]:
            R = r["R"]; l2 = r["l2"]
            dc = R[:, 4]; med = np.median(dc)
            dense = dc > med
            e, mass, var, lmax = R[dense, 0], R[dense, 1], R[dense, 2], R[dense, 3]
            spec = lmax * var; poin = l2 * mass
            beat = np.mean(spec < poin)
            print(f"  {lab} n={r['n']}: dense apices={int(dense.sum())}  "
                  f"mean λ_max·var={spec.mean():.4f}  mean λ₂·mass={poin.mean():.4f}  "
                  f"spec<poin on {100*beat:.0f}%")


if __name__ == "__main__":
    main()
