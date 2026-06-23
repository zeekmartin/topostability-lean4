"""
Min-degree weighted Fiedler measure. Edge measure mu_e = g_e^2/lam (sum mu = 1).
  B2'_unord/lam = E_mu[min(d_a,d_b)-1].  d_eff = Sum_v d_v f_v^2 = E_nu[d_v] (nu_v=f_v^2, ||f||=1).
Lean target B2'_ord<=2lam*degQuad  <=>  E_mu[min-1] <= d_eff  (SHARP; user's 2*d_eff is loose).
Tasks: test E_mu[min-1]<=d_eff and <=2d_eff and sharper E_mu[min]<=d_eff; buckets; correlations;
Chebyshev E_mu[min] vs vertex Fiedler degree average.
Run: python conjecture_B_min_degree_measure.py
"""
import numpy as np
import networkx as nx
from collections import defaultdict


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f))
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    g2 = np.array([(f[a] - f[b]) ** 2 for a, b in edges])
    mn = np.array([min(d[a], d[b]) for a, b in edges])
    lam_e = g2.sum()                                  # = lam (||f||=1)
    mu = g2 / lam_e
    E_min_m1 = float((mu * (mn - 1)).sum())           # E_mu[min-1] = B2'_unord/lam
    E_min = float((mu * mn).sum())                    # E_mu[min]
    # correlations (unweighted over edges) and mu-weighted covariance
    corr_min_g2 = np.corrcoef(mn, g2)[0, 1] if mn.std() > 0 else 0.0
    corr_min_mu = corr_min_g2                         # mu prop g2
    Emin_uniform = mn.mean()                          # uniform edge avg of min
    cov_mu = float((mu * mn).sum() - mn.mean() * (mu).sum())  # E_mu[min]-E_unif[min] (mu sums to 1)
    # buckets by min-degree
    buckets = defaultdict(float)
    for k, m in zip(mn, mu): buckets[int(k)] += m
    return dict(n=n, lam=lam, d_eff=d_eff, E_min_m1=E_min_m1, E_min=E_min,
                r_md=E_min_m1 / d_eff if d_eff > 0 else 0.0,            # vs d_eff (sharp)
                r_md2=E_min_m1 / (2 * d_eff) if d_eff > 0 else 0.0,    # vs 2d_eff (loose)
                r_minfull=E_min / d_eff if d_eff > 0 else 0.0,         # E_mu[min]/d_eff
                corr=corr_min_g2, Emin_uniform=Emin_uniform, cov_mu=cov_mu,
                buckets=dict(buckets), regular=(d.max() == d.min()))


def corpus():
    out = []; rng = np.random.default_rng(0)
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    def star(kc, ks):
        G = nx.complete_graph(kc)
        for i in range(ks): G.add_edge(0, kc + i)
        return G
    for nn in [30, 50, 80]:
        for q in [0.3, 0.5, 0.7, 0.9]: out.append((f"deg2d{nn}_{q}", "TYPEA", d2(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", "TYPEA", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", "CLIQUESTAR", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", "TYPEB", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8)]: out.append((f"barb{k}_{l}", "TYPEB", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", "RANDOM", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, nn // 2]:
            if 3 <= r < nn and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", "REGULAR", nx.random_regular_graph(r, nn, seed=1)))
    for nn in [10, 20, 30, 50]: out.append((f"K{nn}", "REGULAR", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, cl, q) for nm, cl, G in corpus() for q in [quant(G)] if q is not None]

    print("=" * 92)
    print("TASK 1/2 — E_mu[min-1] vs d_eff (SHARP = Lean leaf) and 2d_eff (loose); E_mu[min]/d_eff")
    print("=" * 92)
    sharp = sum(1 for _, _, q in data if q['E_min_m1'] <= q['d_eff'] + 1e-7)
    loose = sum(1 for _, _, q in data if q['E_min_m1'] <= 2 * q['d_eff'] + 1e-7)
    minfull = sum(1 for _, _, q in data if q['E_min'] <= q['d_eff'] + 1e-7)
    print(f"  E_mu[min-1] <= d_eff  (SHARP, Lean): {sharp}/{len(data)}")
    print(f"  E_mu[min-1] <= 2d_eff (loose)      : {loose}/{len(data)}")
    print(f"  E_mu[min]   <= d_eff  (sharper?)   : {minfull}/{len(data)}")

    print("\n" + "=" * 92)
    print("extremizer of E_mu[min-1]/d_eff (-> 1 = sharp); and E_mu[min]/d_eff")
    print("=" * 92)
    print(f"  {'graph':12s} {'class':>11} {'Emu[min-1]/deff':>15} {'Emu[min]/deff':>13} {'corr(min,g2)':>13}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['r_md'])[:14]:
        print(f"  {nm:12s} {cl:>11} {q['r_md']:15.4f} {q['r_minfull']:13.4f} {q['corr']:13.3f}")

    print("\n" + "=" * 92)
    print("TASK 3 — min-degree buckets: do HIGH-min buckets carry LOW mu-mass?")
    print("=" * 92)
    for nm in ["deg2d80_0.9", "twin80_2", "star12_8", "gnp40_0.5", "K20"]:
        q = dict((n_, qq) for n_, _, qq in data).get(nm)
        if q is None: continue
        bk = sorted(q['buckets'].items())
        s = "  ".join(f"k={k}:{m:.3f}" for k, m in bk[:6])
        if len(bk) > 6: s += f"  ...(+{len(bk)-6})  k_max={bk[-1][0]}:{bk[-1][1]:.3f}"
        print(f"  {nm:12s} d_eff={q['d_eff']:.2f}: {s}")
    print("  (mass concentrates on LOW-min-degree buckets => E_mu[min] stays small)")

    print("\n" + "=" * 92)
    print("TASK 4 — anti-correlation corr(min-degree, g^2) by class")
    print("=" * 92)
    by = defaultdict(list)
    for nm, cl, q in data: by[cl].append(q['corr'])
    for cl, rs in sorted(by.items()):
        print(f"  {cl:12s}: mean corr(min,g2)={np.mean(rs):+.3f}  range [{min(rs):+.3f},{max(rs):+.3f}]")
    allc = [q['corr'] for _, _, q in data]
    print(f"  ALL: mean={np.mean(allc):+.3f} (negative => anti-correlation: high-min edges low gradient)")

    print("\n" + "=" * 92)
    print("TASK 5 — Chebyshev: E_mu[min] vs uniform-edge E[min]; and vs d_eff")
    print("=" * 92)
    cheb = sum(1 for _, _, q in data if q['E_min'] <= q['Emin_uniform'] + 1e-7)
    print(f"  E_mu[min] <= uniform-edge mean(min): {cheb}/{len(data)} (Chebyshev/rearrangement form)")
    print(f"  {'graph':12s} {'class':>11} {'Emu[min]':>9} {'unif[min]':>10} {'d_eff':>8}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['r_minfull'])[:8]:
        print(f"  {nm:12s} {cl:>11} {q['E_min']:9.3f} {q['Emin_uniform']:10.3f} {q['d_eff']:8.3f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  SHARP E_mu[min-1]<=d_eff: {sharp}/{len(data)}; E_mu[min]<=d_eff: {minfull}/{len(data)}; "
          f"mean corr(min,g2)={np.mean(allc):+.3f}")


if __name__ == "__main__":
    main()
