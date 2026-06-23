"""
Exact identity for Sum_e min(d_a,d_b) g^2 via the Fiedler equation.
  min = (1/2)((d_a+d_b) - |d_a-d_b|)  => Sum_e min g^2 = (1/2)(W - I),
    W = Sum_e(d_a+d_b)g^2 = Sum_v d_v D_v,  I = Sum_e|d_a-d_b|g^2 (>=0).
  Fiedler: D_v = (2lam-d_v)f_v^2 + P_v (P_v=Sum_{u~v}f_u^2) => W = 2 lam d_eff - A,
    A = Sum_e (d_a-d_b)(f_a^2-f_b^2) (signed assortativity term).
  => B2'_unord = Sum_e(min-1)g^2 = lam(d_eff-1) - (1/2)(A + I).
  Lean leaf B2'_ord<=2lam degQuad  <=>  B2'_unord<=lam d_eff  <=>  A + I >= -2 lam.
Run: python conjecture_B_minus_one_identity.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A_ = nx.to_numpy_array(G); d = A_.sum(1); L = np.diag(d) - A_
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    d_eff = float(d @ (f * f))
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A_[i, j] > 0]
    g2 = np.array([(f[a] - f[b]) ** 2 for a, b in edges])
    summ = np.array([d[a] + d[b] for a, b in edges])
    diff = np.array([abs(d[a] - d[b]) for a, b in edges])
    mn = np.array([min(d[a], d[b]) for a, b in edges])
    lam_e = g2.sum()
    W = float((summ * g2).sum())
    I = float((diff * g2).sum())
    Sum_min = float((mn * g2).sum())
    Asrt = float(sum((d[a] - d[b]) * (f[a] ** 2 - f[b] ** 2) for a, b in edges))
    Dv = np.array([sum((f[v] - f[u]) ** 2 for u in range(n) if A_[v, u] > 0) for v in range(n)])
    Pv = np.array([sum(f[u] ** 2 for u in range(n) if A_[v, u] > 0) for v in range(n)])
    # identities
    id_Dv = float(np.max(np.abs(Dv - ((2 * lam - d) * f ** 2 + Pv))))          # D_v identity
    id_W = abs(W - float((d * Dv).sum()))                                       # W = Sum d_v D_v
    id_WA = abs(W - (2 * lam_e * d_eff - Asrt))                                 # W = 2lam d_eff - A
    id_min = abs(Sum_min - 0.5 * (W - I))                                       # min = (W-I)/2
    B2u = Sum_min - lam_e                                                       # B2'_unord
    id_B2 = abs(B2u - (lam_e * (d_eff - 1) - 0.5 * (Asrt + I)))                # B2' identity
    return dict(n=n, lam=lam_e, d_eff=d_eff, W=W, I=I, Asrt=Asrt, Sum_min=Sum_min, B2u=B2u,
                E_min=Sum_min / lam_e, AI=Asrt + I,
                id_Dv=id_Dv, id_W=id_W, id_WA=id_WA, id_min=id_min, id_B2=id_B2,
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
    print("TASK 3/5 — EXACT IDENTITIES (max error over corpus)")
    print("=" * 92)
    print(f"  D_v = (2λ-d_v)f_v² + P_v          : max err {max(q['id_Dv'] for _,_,q in data):.2e}")
    print(f"  W = Σ_v d_v D_v                   : max err {max(q['id_W'] for _,_,q in data):.2e}")
    print(f"  W = 2λ·d_eff - A  (A=assort)     : max err {max(q['id_WA'] for _,_,q in data):.2e}")
    print(f"  Σ_e min g² = ½(W - I)            : max err {max(q['id_min'] for _,_,q in data):.2e}")
    print(f"  ★ B2'_unord = λ(d_eff-1) - ½(A+I): max err {max(q['id_B2'] for _,_,q in data):.2e}")

    print("\n" + "=" * 92)
    print("TASK 1/4 — the reduced inequality. Leaf <=> A + I >= -2λ. Also test sharper -λ.")
    print("=" * 92)
    leaf = sum(1 for _, _, q in data if q['AI'] >= -2 * q['lam'] - 1e-7)
    half = sum(1 for _, _, q in data if q['AI'] >= -q['lam'] - 1e-7)
    pos = sum(1 for _, _, q in data if q['AI'] >= -1e-7)
    print(f"  A+I >= -2λ  (= Lean leaf, E_μ[min]<=d_eff+1)   : {leaf}/{len(data)}")
    print(f"  A+I >= -λ   (= E_μ[min]<=d_eff+1/2, user cand) : {half}/{len(data)}")
    print(f"  A+I >= 0    (= E_μ[min]<=d_eff)                : {pos}/{len(data)}")
    print(f"  E_μ[min] = d_eff - (A+I)/(2λ); A+I<0 <=> E_μ[min]>d_eff")

    print("\n" + "=" * 92)
    print("TASK 4 — A (assortativity) and I (imbalance) by class; which makes A+I negative?")
    print("=" * 92)
    print(f"  {'graph':12s} {'class':>11} {'A':>9} {'I':>9} {'A+I':>9} {'-2λ':>9} {'A alone>=-2λ?':>13}")
    for nm, cl, q in sorted(data, key=lambda x: x[2]['AI'] / max(x[2]['lam'], 1e-9))[:14]:
        aok = "yes" if q['Asrt'] >= -2 * q['lam'] - 1e-7 else "NO"
        print(f"  {nm:12s} {cl:>11} {q['Asrt']:9.3f} {q['I']:9.3f} {q['AI']:9.3f} {-2*q['lam']:9.3f} {aok:>13}")

    print("\n" + "=" * 92)
    print("TASK 2 — is A alone >= -2λ (sufficient since I>=0)? and sign of A")
    print("=" * 92)
    Aonly = sum(1 for _, _, q in data if q['Asrt'] >= -2 * q['lam'] - 1e-7)
    Apos = sum(1 for _, _, q in data if q['Asrt'] >= -1e-7)
    print(f"  A >= -2λ (sufficient for leaf since I>=0): {Aonly}/{len(data)}")
    print(f"  A >= 0 (assortativity nonneg)            : {Apos}/{len(data)}")
    print(f"  min A/λ = {min(q['Asrt']/q['lam'] for _,_,q in data):.3f} (need >= -2 for A-only route)")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  EXACT: B2'_unord = λ(d_eff-1) - ½(A+I), A=Σ_e(d_a-d_b)(f_a²-f_b²), I=Σ_e|d_a-d_b|g²>=0")
    print(f"  Leaf <=> A+I >= -2λ: {leaf}/{len(data)}; A alone >= -2λ: {Aonly}/{len(data)}")


if __name__ == "__main__":
    main()
