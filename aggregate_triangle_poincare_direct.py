"""
Direct proof attempts for aggregate_triangle_poincare: T <= 2*lam*degQuad (Lean ordered;
T_unord <= lam*degQuad). T = Sum_c E_{G[N(c)]} (apex). NO B2'/min-degree bound.
Routes:
 (K) subgraph<=complete: E_{G[N(c)]}<=E_{K_{N(c)}}=d_c P_c-(d_c-lam)^2 f_c^2 => cond A>=lam(d_eff-lam).
 (apex) per-apex E_{N(c)}<=2lam P_c (known ~6% fail) vs aggregate.
 (lmax) E_{N(c)}<=lmax(L_{G[N(c)]})*Var_{N(c)}.
Run: python aggregate_triangle_poincare_direct.py
"""
import numpy as np
import networkx as nx


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f)); A2 = A @ A
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    T_un = sum(A2[a, b] * (f[a] - f[b]) ** 2 for a, b in edges)          # unordered T
    RHS = lam * d_eff                                                     # T_un <= RHS target
    # signed assortativity A
    s = A @ d
    Asrt = float(((d ** 2 - s) * f ** 2).sum())
    # K-bound: T_un <= Sum s_v f^2 - Sum (d_c-lam)^2 f_c^2
    Kbound = float((s * f ** 2).sum() - ((d - lam) ** 2 * f ** 2).sum())
    cond_K = Asrt - lam * (d_eff - lam)                                   # >=0 means K-route valid
    # per-apex Poincare: E_{N(c)} <= 2 lam P_c ? count violations; aggregate Sum E = T_un... wait
    # E_{G[N(c)]} unordered Dirichlet on neighbors; P_c = sum_{v~c} f_v^2
    apex_viol = 0; apex_tot = 0
    Ec_sum = 0.0; lmax_bound = 0.0
    for c in range(n):
        Nc = [v for v in range(n) if A[c, v] > 0]
        if len(Nc) < 2:
            apex_tot += 1; continue
        Ec = sum((f[a] - f[b]) ** 2 for ii, a in enumerate(Nc) for b in Nc[ii + 1:] if A[a, b] > 0)
        Pc = sum(f[v] ** 2 for v in Nc)
        Ec_sum += Ec
        apex_tot += 1
        if Ec > 2 * lam * Pc + 1e-9: apex_viol += 1   # per-apex local Poincare (the ~6%)
        # lmax of induced subgraph Laplacian
        sub = A[np.ix_(Nc, Nc)]; ds = sub.sum(1); Lsub = np.diag(ds) - sub
        lmax = np.linalg.eigvalsh(Lsub)[-1] if len(Nc) > 1 else 0.0
        meanf = sum(f[v] for v in Nc) / len(Nc)
        Var = sum((f[v] - meanf) ** 2 for v in Nc)
        lmax_bound += lmax * Var
    return dict(n=n, lam=lam, d_eff=d_eff, T_un=T_un, RHS=RHS,
                ratio=T_un / RHS if RHS > 0 else 0.0,
                Asrt=Asrt, Kbound=Kbound, K_ratio=Kbound / RHS if RHS > 0 else 9.9,
                cond_K=cond_K, apex_viol=apex_viol, apex_tot=apex_tot,
                lmax_ratio=lmax_bound / RHS if RHS > 0 else 9.9,
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
        for q in [0.01, 0.03, 0.06, 0.1, 0.15, 0.3, 0.6, 0.9]: out.append((f"deg2d{nn}_{q}", "TYPEA", d2(nn, q, 7)))
    for N in [30, 60]:
        for dd in [2, 3]: out.append((f"twin{N}_{dd}", "TYPEA", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", "CLIQUESTAR", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", "TYPEB", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8)]: out.append((f"barb{k}_{l}", "TYPEB", nx.barbell_graph(k, l)))
    for nn in [25, 40]:
        for q in [0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", "RANDOM", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, nn // 2]:
            if 3 <= r < nn and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", "REGULAR", nx.random_regular_graph(r, nn, seed=1)))
    out.append(("cocktail6", "MULTIPART", nx.complete_multipartite_graph(*([2] * 6))))
    out.append(("Kmp444", "MULTIPART", nx.complete_multipartite_graph(4, 4, 4)))
    for nn in [10, 20, 30, 50]: out.append((f"K{nn}", "REGULAR", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, cl, q) for nm, cl, G in corpus() for q in [analyze(G)] if q is not None]
    print(f"  {len(data)} graphs; aggregate T<=2λdegQuad holds: "
          f"{sum(1 for _,_,q in data if q['ratio']<=1+1e-7)}/{len(data)}")

    print("\n" + "=" * 92)
    print("TASK 5 — extremal family for T/(2λ·degQuad) (= T_un/RHS); ratio->1 = tight")
    print("=" * 92)
    print(f"  {'graph':12s} {'class':>11} {'T/RHS':>8} {'reg':>5}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['ratio'])[:12]:
        print(f"  {nm:12s} {cl:>11} {q['ratio']:8.4f} {str(q['regular']):>5}")

    print("\n" + "=" * 92)
    print("TASK 1/3 — K-bound route: T_un<=Sum s_v f^2-Sum(d_c-λ)^2 f_c^2; valid iff A>=λ(d_eff-λ)")
    print("=" * 92)
    kok = sum(1 for _, _, q in data if q['cond_K'] >= -1e-7)
    kvalid = sum(1 for _, _, q in data if q['K_ratio'] <= 1 + 1e-7)
    print(f"  condition A>=λ(d_eff-λ): {kok}/{len(data)}")
    print(f"  K-bound itself <= RHS (Kbound/RHS<=1): {kvalid}/{len(data)}")
    print(f"  {'graph':12s} {'class':>11} {'T/RHS':>7} {'Kbound/RHS':>11} {'condK(A-λ(deff-λ))':>18}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['K_ratio'])[:10]:
        print(f"  {nm:12s} {cl:>11} {q['ratio']:7.3f} {q['K_ratio']:11.3f} {q['cond_K']:18.3f}")
    print("  (K-bound tight at K_n [G[N(c)] complete]; LOSSY/invalid when G[N(c)] sparse)")

    print("\n" + "=" * 92)
    print("TASK 2 — per-apex local Poincare E_{N(c)}<=2λ P_c: violation rate (the ~6%)")
    print("=" * 92)
    tv = sum(q['apex_viol'] for _, _, q in data); tt = sum(q['apex_tot'] for _, _, q in data)
    print(f"  per-apex violations: {tv}/{tt} ({100*tv/tt:.1f}%) — local fails, aggregate (T<=RHS) holds")
    lmaxok = sum(1 for _, _, q in data if q['lmax_ratio'] <= 1 + 1e-7)
    print(f"  lmax(L_sub)*Var aggregate <= RHS: {lmaxok}/{len(data)} "
          f"(max {max(q['lmax_ratio'] for _,_,q in data):.2f})")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    mx = max(data, key=lambda x: x[2]['ratio'])
    print(f"  aggregate extremal: {mx[0]} ({mx[1]}) T/RHS={mx[2]['ratio']:.4f} (regular={mx[2]['regular']})")
    print(f"  K-route condition A>=λ(d_eff-λ): {kok}/{len(data)} (fails => K-bound too lossy for sparse)")


if __name__ == "__main__":
    main()
