"""
Covariance route for aggregate E_mu[t_e] <= d_eff, mu(e)=g^2/lam (normalized, sum=1).
E_mu[t]=T_unord/lam = t_bar + m*Cov_unif(t,g^2)/lam (identity).
Conjecture <=> Cov(t,g^2) <= (lam/m)(d_eff - t_bar).
Test (a) Cov<=0 and (b) t_bar<=d_eff separately.
Run: python conjecture_B_covariance_route.py
"""
import numpy as np
import networkx as nx


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f))
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    m = len(edges)
    t = np.array([A2[a, b] for a, b in edges])
    g2 = np.array([(f[a] - f[b]) ** 2 for a, b in edges])
    lam_e = g2.sum()                                  # = lam
    T = float((t * g2).sum())                         # T_unord
    E_mu_t = T / lam_e                                # E_mu[t]
    t_bar = t.mean()
    g2_bar = g2.mean()                               # = lam/m
    Cov = float((t * g2).mean() - t_bar * g2_bar)    # Cov_unif(t,g2)
    corr = np.corrcoef(t, g2)[0, 1] if t.std() > 0 and g2.std() > 0 else 0.0
    # identity check
    id_err = abs(E_mu_t - (t_bar + m * Cov / lam_e))
    # conjecture pieces
    rhs_cov = (lam_e / m) * (d_eff - t_bar)
    return dict(n=n, m=m, lam=lam_e, d_eff=d_eff, E_mu_t=E_mu_t, t_bar=t_bar, Cov=Cov, corr=corr,
                id_err=id_err, rhs_cov=rhs_cov,
                aggr_holds=(E_mu_t <= d_eff + 1e-9),
                a_cov_le0=(Cov <= 1e-12),
                b_tbar_le_deff=(t_bar <= d_eff + 1e-9),
                regular=(d.max() == d.min()))


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
        Gr = nx.complete_graph(kc)
        for i in range(ks): Gr.add_edge(0, kc + i)
        return Gr
    for nn in [40, 60, 80]:
        for q in [0.05, 0.1, 0.2, 0.4, 0.6, 0.85]: out.append((f"deg2d{nn}_{q}", "TYPEA", d2(nn, q, 7)))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", "TYPEA", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", "CLIQUESTAR", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", "TYPEB", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8)]: out.append((f"barb{k}_{l}", "TYPEB", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.1, 0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", "RANDOM", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, nn // 2]:
            if 3 <= r < nn and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", "REGULAR", nx.random_regular_graph(r, nn, seed=1)))
    out.append(("cocktail6", "MULTIPART", nx.complete_multipartite_graph(*([2] * 6))))
    out.append(("Kmp444", "MULTIPART", nx.complete_multipartite_graph(4, 4, 4)))
    for nn in [10, 20, 30, 50]: out.append((f"K{nn}", "REGULAR", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, cl, q) for nm, cl, G in corpus() for q in [analyze(G)] if q is not None]
    print(f"  {len(data)} graphs; aggregate E_μ[t]<=d_eff: {sum(1 for _,_,q in data if q['aggr_holds'])}/{len(data)}")

    print("\n" + "=" * 96)
    print("TASK 2 — identity E_μ[t] = t_bar + m·Cov(t,g²)/λ  (max error)")
    print("=" * 96)
    print(f"  max|E_μ[t] - (t_bar + m·Cov/λ)| = {max(q['id_err'] for _,_,q in data):.2e}")

    print("\n" + "=" * 96)
    print("TASK 5 — (a) Cov(t,g²)<=0  and  (b) t_bar<=d_eff  separately")
    print("=" * 96)
    a_ok = sum(1 for _, _, q in data if q['a_cov_le0'])
    b_ok = sum(1 for _, _, q in data if q['b_tbar_le_deff'])
    both = sum(1 for _, _, q in data if q['a_cov_le0'] and q['b_tbar_le_deff'])
    print(f"  (a) Cov(t,g²) <= 0 (anti-correlation): {a_ok}/{len(data)}")
    print(f"  (b) t_bar <= d_eff                   : {b_ok}/{len(data)}")
    print(f"  (a) AND (b)                          : {both}/{len(data)}")

    print("\n" + "=" * 96)
    print("TASK 6 — where (a) and (b) fail")
    print("=" * 96)
    print("  (a) Cov>0 failures:")
    for nm, cl, q in data:
        if not q['a_cov_le0']: print(f"    {nm:12s} ({cl}) Cov={q['Cov']:.4f} corr={q['corr']:.3f}")
    print("  (b) t_bar>d_eff failures (sample, sorted by t_bar/d_eff):")
    bf = [(nm, cl, q) for nm, cl, q in data if not q['b_tbar_le_deff']]
    for nm, cl, q in sorted(bf, key=lambda x: -x[2]['t_bar'] / x[2]['d_eff'])[:10]:
        print(f"    {nm:12s} ({cl}) t_bar={q['t_bar']:.2f} d_eff={q['d_eff']:.2f} "
              f"ratio={q['t_bar']/q['d_eff']:.1f}  (E_μ[t]={q['E_mu_t']:.2f} still <= d_eff)")

    print("\n" + "=" * 96)
    print("TASK 3 — covariance bound Cov <= (λ/m)(d_eff-t_bar); when t_bar>d_eff RHS<0 (hard)")
    print("=" * 96)
    print(f"  {'graph':12s} {'Cov':>9} {'RHS=(λ/m)(deff-tbar)':>20} {'E_μ[t]':>7} {'d_eff':>7} {'t_bar':>7}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['E_mu_t'] / x[2]['d_eff'])[:8]:
        print(f"  {nm:12s} {q['Cov']:9.4f} {q['rhs_cov']:20.5f} {q['E_mu_t']:7.3f} {q['d_eff']:7.3f} {q['t_bar']:7.2f}")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  identity exact ({max(q['id_err'] for _,_,q in data):.0e}); (a) Cov<=0: {a_ok}/{len(data)}; "
          f"(b) t_bar<=d_eff: {b_ok}/{len(data)}; both: {both}/{len(data)}")
    if both < len(data):
        print(f"  => split (a)+(b) FAILS ({'(b) breaks on bottleneck' if b_ok<len(data) else '(a) breaks'}); "
              f"need quantitative Cov bound (= aggregate).")


if __name__ == "__main__":
    main()
