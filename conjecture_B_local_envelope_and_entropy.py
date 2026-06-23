"""
Two attacks on the magnitude of anti-correlation.
PART A: local envelope g_e^2 <= C/(t_e+1)^alpha; does it close T <= 2lam*d_eff?
PART B: entropy/Chernoff/Pinsker on mu(e)=g^2/lam (normalized). Likely wrong-direction.
Run: python conjecture_B_local_envelope_and_entropy.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f))
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    m = len(edges)
    t = np.array([float(A2[a, b]) for a, b in edges])
    g2 = np.array([(f[a] - f[b]) ** 2 for a, b in edges])
    if t.sum() == 0: return None
    lam_e = g2.sum()
    return dict(n=n, m=m, lam=lam_e, d_eff=d_eff, t=t, g2=g2,
                E_mu_t=float((t * g2).sum()) / lam_e, t_bar=t.mean(),
                aggr_rhs=lam_e * d_eff, T=float((t * g2).sum()))


def corpus():
    out = []; rng = np.random.default_rng(0)
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    for nn in [40, 60, 80]:
        for q in [0.1, 0.3, 0.6, 0.9]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    for N in [30, 50]:
        for dd in [2, 3]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for nn in [25, 40]:
        for q in [0.3, 0.6]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20]: out.append((f"rr{nn}_6", nx.random_regular_graph(6, nn, seed=1)))
    for nn in [12, 20, 30]: out.append((f"K{nn}", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [quant(G)] if q is not None]
    print(f"  {len(data)} graphs")

    print("\n" + "=" * 92)
    print("PART A — local envelope g² ≤ C(G)/(t+1)^α; does T-bound ≤ 2λ·d_eff? (per α)")
    print("=" * 92)
    print("  For each α: C_α(G)=max_e g²(t+1)^α; T_bound=C_α·Σ t/(t+1)^α; check T_bound ≤ 2λd_eff")
    print(f"  {'α':>5} {'envelope holds':>15} {'T_bound≤2λd_eff':>16} {'max T_bound/RHS':>16}")
    for alpha in [0.25, 0.5, 0.75, 1.0]:
        ok = 0; mx = 0.0
        for nm, q in data:
            C = float(np.max(q['g2'] * (q['t'] + 1) ** alpha))     # envelope const (per graph)
            Tb = C * float((q['t'] / (q['t'] + 1) ** alpha).sum())
            r = Tb / q['aggr_rhs']
            mx = max(mx, r)
            if r <= 1 + 1e-9: ok += 1
        print(f"  {alpha:5.2f} {'(C=max, exact)':>15} {ok:>9}/{len(data)} {mx:16.3f}")
    print("  (envelope is exact by construction; question is whether the T-bound beats RHS)")

    print("\n" + "=" * 92)
    print("PART A4 — which α minimizes max T_bound/RHS?")
    print("=" * 92)
    best = None
    for alpha in np.linspace(0, 2, 9):
        mx = max((float(np.max(q['g2'] * (q['t'] + 1) ** alpha)) *
                  float((q['t'] / (q['t'] + 1) ** alpha).sum())) / q['aggr_rhs'] for _, q in data)
        if best is None or mx < best[1]: best = (alpha, mx)
        print(f"  α={alpha:.2f}: max T_bound/RHS = {mx:.3f}")
    print(f"  best α={best[0]:.2f} (max ratio {best[1]:.3f}); <=1 means the envelope route works")

    print("\n" + "=" * 92)
    print("PART B1 — entropy H(μ)/log(m)  (μ_e=g²/λ)")
    print("=" * 92)
    for nm, q in sorted(data, key=lambda x: x[1]['E_mu_t'] / x[1]['d_eff'])[-6:]:
        mu = q['g2'] / q['lam']; mu = mu[mu > 1e-15]
        H = -float((mu * np.log(mu)).sum())
        print(f"  {nm:12s} H(μ)/log(m)={H/np.log(q['m']):.3f}  (E_μ[t]={q['E_mu_t']:.2f} d_eff={q['d_eff']:.2f})")

    print("\n" + "=" * 92)
    print("PART B2 — Chernoff inf_s log M(s)/s  vs  E_μ[t]  (should NOT beat E_μ[t])")
    print("=" * 92)
    for nm, q in sorted(data, key=lambda x: -x[1]['E_mu_t'])[:5]:
        mu = q['g2'] / q['lam']
        best_ch = min((np.log(float((mu * np.exp(s * q['t'])).sum())) / s) for s in [0.01, 0.05, 0.1, 0.3, 1.0])
        print(f"  {nm:12s} inf_s logM(s)/s={best_ch:.3f}  E_μ[t]={q['E_mu_t']:.3f} d_eff={q['d_eff']:.3f} "
              f"({'beats' if best_ch < q['E_mu_t']-1e-6 else 'NO improvement over E_μ[t]'})")

    print("\n" + "=" * 92)
    print("PART B4 — Pinsker direction. KL, |dev| bound t_max√(KL/2); is it the WRONG sign?")
    print("=" * 92)
    for nm, q in sorted(data, key=lambda x: -x[1]['t_bar'] / x[1]['d_eff'])[:5]:
        mu = q['g2'] / q['lam']; mup = mu[mu > 1e-15]
        KL = float((mup * np.log(q['m'] * mup)).sum())
        actual_dev = q['E_mu_t'] - q['t_bar']                      # negative (anti-corr)
        pinsker_mag = q['t'].max() * np.sqrt(KL / 2)               # upper bound on |dev|
        print(f"  {nm:12s} dev={actual_dev:+.2f} |Pinsker bound|={pinsker_mag:.2f} "
              f"t_bar={q['t_bar']:.1f} d_eff={q['d_eff']:.2f}  "
              f"(need dev<={q['d_eff']-q['t_bar']:+.1f}; Pinsker bounds |dev| from ABOVE => useless)")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  PART A: best envelope α gives max T_bound/RHS = {best[1]:.3f} "
          f"({'WORKS' if best[1]<=1 else 'FAILS — envelope too loose'})")
    print("  PART B: Chernoff inf = E_μ[t] (no gain); Pinsker bounds |dev| from above (wrong direction).")
    print("  => entropic/transport tools are MISALIGNED (need dev large-negative; they cap |dev|).")


if __name__ == "__main__":
    main()
