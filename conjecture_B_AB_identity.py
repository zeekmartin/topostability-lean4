"""
Exact identity for A-B (irregular). Derived:
  A = Sum_v mdeg_v D_v - C,  Sum_v mdeg_v D_v = 2(n-1)lam - W  [W=Sum_e(d_a+d_b)g^2]
  B = lam(n-2-2 d_eff + lam)
  => A-B = lam(n-lam) + 2 lam d_eff - W - C   [C=Sum_e tbar_e g^2]
  via tbar_e = n - d_a - d_b + t_e: C = n lam - W + T  => A-B = lam(2 d_eff - lam) - T (=gap+D).
R := (A-B) - lam(d_eff+1-lam) = lam(n-1) + lam d_eff - W - C = lam(d_eff-1) - T.
Tests: identity; R sign; R-D; R structure; closure.
Run: python conjecture_B_AB_identity.py
"""
import numpy as np
import networkx as nx


def quant(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); d_eff = float(d @ (f * f)); A2 = A @ A
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    nonedges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] == 0]
    g2 = {(a, b): (f[a] - f[b]) ** 2 for (a, b) in edges}
    Aterm = sum(sum(1 for c in range(n) if c != a and c != b and (A[a, c] == 0 or A[b, c] == 0)) * g2[(a, b)]
                for (a, b) in edges)
    Bterm = lam * sum((f[i] + f[j]) ** 2 for i, j in nonedges)
    Dterm = lam * S ** 2 / m
    W = sum((d[a] + d[b]) * g2[(a, b)] for (a, b) in edges)
    C = sum(sum(1 for c in range(n) if c != a and c != b and A[a, c] == 0 and A[b, c] == 0) * g2[(a, b)]
            for (a, b) in edges)
    T = sum(A2[a, b] * g2[(a, b)] for (a, b) in edges)
    AB = Aterm - Bterm
    # identity check
    id1 = lam * (n - lam) + 2 * lam * d_eff - W - C
    id2 = lam * (2 * d_eff - lam) - T
    R = AB - lam * (d_eff + 1 - lam)
    Rcirc = lam * (d_eff - 1) - T
    # structure candidate: degree-variance-at-f
    dvarf = float((d * d) @ (f * f)) - d_eff ** 2   # fD^2f - (fDf)^2
    sum_dminus_sq = float(np.sum((d - d_eff) ** 2 * f * f))  # Sum (d_v-d_eff)^2 f_v^2
    return dict(n=n, lam=lam, d_eff=d_eff, A=Aterm, B=Bterm, D=Dterm, W=W, C=C, T=T, AB=AB,
                id1=id1, id2=id2, R=R, Rcirc=Rcirc, S2m=S ** 2 / m, dvarf=dvarf,
                sum_dminus_sq=sum_dminus_sq, regular=(d.max() == d.min()),
                gap=AB - Dterm)


def corpus():
    out = []; rng = np.random.default_rng(0)
    def deg2dense(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1)
        H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    for nn in [30, 50, 80]:
        for q in [0.4, 0.6, 0.8, 0.9]: out.append((f"deg2d{nn}_{q}", deg2dense(nn, q, int(rng.integers(1e9)))))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", nx.lollipop_graph(k, l)))
    out.append(("barb8_8", nx.barbell_graph(8, 8)))
    for nn in [25, 40]:
        for q in [0.3, 0.5, 0.7]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20]: out.append((f"rr{nn}_6", nx.random_regular_graph(6, nn, seed=1)))
    for nn in [12, 20]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [30]:
        for kd in [1, 6]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kd: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [quant(G)] if q is not None]
    print(f"  {len(data)} graphs")

    print("\n" + "=" * 92)
    print("TASK 1 — exact identity A-B = λ(n-λ)+2λd_eff-W-C  (and = λ(2d_eff-λ)-T)")
    print("=" * 92)
    e1 = max(abs(q['AB'] - q['id1']) for _, q in data)
    e2 = max(abs(q['AB'] - q['id2']) for _, q in data)
    print(f"  max|A-B - [λ(n-λ)+2λd_eff-W-C]| = {e1:.2e}")
    print(f"  max|A-B - [λ(2d_eff-λ)-T]|     = {e2:.2e}")

    print("\n" + "=" * 92)
    print("TASK 2/3 — R = (A-B) - λ(d_eff+1-λ) = λ(d_eff-1)-T. sign of R; R for regular; min")
    print("=" * 92)
    eR = max(abs(q['R'] - q['Rcirc']) for _, q in data)
    print(f"  max|R - [λ(d_eff-1)-T]| = {eR:.2e} (identity check)")
    Rok = sum(1 for _, q in data if q['R'] >= -1e-9)
    mnR = min(data, key=lambda x: x[1]['R'])
    print(f"  R >= 0 : {Rok}/{len(data)}; min R = {mnR[1]['R']:.5f} at {mnR[0]}")
    print(f"  (R does NOT vanish for regular: R_reg = λ(n-1-d)-C >=0, =0 only at K_n)")
    for nm, q in [("rr20_6", None), ("K20", None), ("K12", None)]:
        q = dict(data).get(nm)
        if q: print(f"    {nm}: R={q['R']:.4f} (regular={q['regular']})")

    print("\n" + "=" * 92)
    print("TASK 3 — is R >= D? (would give gap>=λ(d_eff+1-λ)>=0). min(R-D)")
    print("=" * 92)
    RD = sum(1 for _, q in data if q['R'] >= q['D'] - 1e-9)
    mnRD = min(data, key=lambda x: x[1]['R'] - x[1]['D'])
    print(f"  R >= D : {RD}/{len(data)}; min(R-D) = {mnRD[1]['R']-mnRD[1]['D']:.5f} at {mnRD[0]}")
    print(f"  (if R<D somewhere, the closure needs R>=0 AND spectral bound, not R>=D)")

    print("\n" + "=" * 92)
    print("TASK 4 — structure of R: variance form? R vs Σ(d_v-d_eff)²f_v², R vs d_var_f")
    print("=" * 92)
    Rv = np.array([q['R'] for _, q in data]); dvf = np.array([q['sum_dminus_sq'] for _, q in data])
    print(f"  corr(R, Σ(d_v-d_eff)²f_v²) = {np.corrcoef(Rv, dvf)[0,1]:+.3f}")
    print(f"  {'graph':12s} {'R':>9} {'Σ(d-d_eff)²f²':>13} {'R/that':>8}")
    for nm, q in sorted(data, key=lambda x: x[1]['R'])[:8]:
        r = q['R'] / q['sum_dminus_sq'] if q['sum_dminus_sq'] > 1e-9 else float('nan')
        print(f"  {nm:12s} {q['R']:9.4f} {q['sum_dminus_sq']:13.4f} {r:8.4f}")

    print("\n" + "=" * 92)
    print("TASK 5 — closure: gap = λ(d_eff+1-λ) + R - D. gap>=0 <= R>=0 AND λ+S²/m<=d_eff+1")
    print("=" * 92)
    spec = sum(1 for _, q in data if q['lam'] + q['S2m'] <= q['d_eff'] + 1 + 1e-9)
    both = sum(1 for _, q in data if q['R'] >= -1e-9 and q['lam'] + q['S2m'] <= q['d_eff'] + 1 + 1e-9)
    gappos = sum(1 for _, q in data if q['gap'] >= -1e-9)
    print(f"  R>=0: {Rok}/{len(data)}; spectral λ+S²/m<=d_eff+1: {spec}/{len(data)}; "
          f"both: {both}/{len(data)}; gap>=0: {gappos}/{len(data)}")
    print("  closure: gap=λ(d_eff+1-λ)+R-D; if R>=0 and (λ+S²/m<=d_eff+1 i.e. D<=λ(d_eff+1-λ)) then")
    print("           gap = [λ(d_eff+1-λ)-D] + R >= 0+0 = 0.")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  identity exact (err {e1:.1e}); R>=0 {Rok}/{len(data)}; R>=D {RD}/{len(data)}; "
          f"closure(R>=0 & spectral) {both}/{len(data)}")


if __name__ == "__main__":
    main()
