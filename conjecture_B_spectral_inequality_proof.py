"""
Prove lam + S^2/m <= d_eff + 1 for the Fiedler.  <=>  f^T A f >= S^2/m - 1  (fAf = d_eff - lam).
Equivalently (TASK5): f^T(D - dd^T/m)f >= lam - 1, i.e. f^T(A + I - dd^T/m)f >= 0.
KEY QUESTION: does A + I - dd^T/m >= 0 on 1-perp (FOR ALL f, => clean matrix proof) or only Fiedler?
Run: python conjecture_B_spectral_inequality_proof.py
"""
import numpy as np
import networkx as nx


def tests(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]
    simple = ev[2] - lam > 1e-7
    f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); d_eff = float(d @ (f * f)); fAf = float(f @ A @ f)
    dbar = 2 * m / n
    # target (Fiedler): fAf >= S^2/m - 1
    target = fAf - (S ** 2 / m - 1)            # >=0 ?
    # CS (TASK2): S^2/m <= 2 d_eff
    cs2 = 2 * d_eff - S ** 2 / m                # >=0 (CS, should always hold); need <= d_eff+1-lam
    cs2_enough = (d_eff + 1 - lam) - 2 * d_eff  # >=0 would mean CS enough (expect <0)
    # TASK3 centered: S^2 <= f^T(D-dbar I)^2 f ; need <= m(d_eff+1-lam)
    Dc = np.diag(d - dbar)
    t3lhs = float(f @ (Dc @ Dc) @ f)           # f^T(D-dbar)^2 f  >= S^2 ? (CS)
    t3_cs = t3lhs - S ** 2                      # >=0 (CS via f perp 1)
    t3_enough = m * (d_eff + 1 - lam) - t3lhs   # >=0 would prove target
    # TASK5 matrix form on 1-perp: M5 = A + I - dd^T/m ; lam_min(P M5 P) >=0 for ALL f? (clean if yes)
    P = np.eye(n) - np.ones((n, n)) / n
    M5 = A + np.eye(n) - np.outer(d, d) / m
    M5p = P @ M5 @ P
    evm = np.linalg.eigvalsh(M5p)
    # smallest eigenvalue on 1-perp (exclude the ~0 from P's kernel direction = 1)
    # P M5 P has 1 in kernel (eigenvalue ~0); the relevant min is over 1-perp
    lam_min_1perp = sorted(evm)[1]             # 2nd smallest (1st is the kernel ~0)
    # also lam_min(D - dd^T/m on 1-perp) vs lam-1
    Mdc = np.diag(d) - np.outer(d, d) / m
    evdc = sorted(np.linalg.eigvalsh(P @ Mdc @ P))
    lmin_dc = evdc[1]
    return dict(n=n, lam=lam, simple=simple, target=target, cs2=cs2, cs2_enough=cs2_enough,
                t3_cs=t3_cs, t3_enough=t3_enough, matrix_min=lam_min_1perp,
                lmin_dc=lmin_dc, lam_m1=lam - 1, d_eff=d_eff, S2m=S ** 2 / m)


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
    for k, l in [(8, 8)]: out.append((f"barb{k}_{l}", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.3, 0.5, 0.7, 0.85]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]: out.append((f"rr{nn}_6", nx.random_regular_graph(6, nn, seed=1)))
    for nn in [12, 20]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [30, 50]:
        for kdel in [1, 4, 10]:
            K = nx.complete_graph(nn); E = list(K.edges()); rng.shuffle(E); rem = 0
            for e in E:
                if rem >= kdel: break
                if K.degree(e[0]) > 2 and K.degree(e[1]) > 2: K.remove_edge(*e); rem += 1
            out.append((f"K{nn}-{rem}", K))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [tests(G)] if q is not None]
    print(f"  {len(data)} connected graphs")

    print("\n" + "=" * 92)
    print("TARGET — Fiedler: fᵀAf >= S²/m - 1  (= lam+S²/m <= d_eff+1)")
    print("=" * 92)
    ok = sum(1 for _, q in data if q['target'] >= -1e-7)
    mn = min(data, key=lambda x: x[1]['target'])
    print(f"  holds: {ok}/{len(data)};  min slack = {mn[1]['target']:.5f} at {mn[0]}")

    print("\n" + "=" * 92)
    print("TASK 5 — MATRIX form: A + I - ddᵀ/m >= 0 on 1⊥ (FOR ALL f => clean proof)?")
    print("=" * 92)
    okm = sum(1 for _, q in data if q['matrix_min'] >= -1e-7)
    mnm = min(data, key=lambda x: x[1]['matrix_min'])
    print(f"  λ_min(A+I-ddᵀ/m | 1⊥) >= 0 : {okm}/{len(data)};  min = {mnm[1]['matrix_min']:.5f} at {mnm[0]}")
    print(f"  => {'CLEAN MATRIX PROOF (holds for all f⊥1)' if okm==len(data) else 'FAILS for some f (matrix form too strong; Fiedler-specific needed)'}")
    # also TASK5b: lam_min(D-ddᵀ/m on 1⊥) >= lam-1 ?
    okdc = sum(1 for _, q in data if q['lmin_dc'] >= q['lam_m1'] - 1e-7)
    print(f"  λ_min(D-ddᵀ/m | 1⊥) >= λ-1 : {okdc}/{len(data)} (TASK5b, stronger)")

    print("\n" + "=" * 92)
    print("TASK 2 — CS S²/m <= 2 d_eff (valid) but enough? (need <= d_eff+1-λ)")
    print("=" * 92)
    cs_valid = sum(1 for _, q in data if q['cs2'] >= -1e-7)
    cs_enough = sum(1 for _, q in data if q['cs2_enough'] >= -1e-7)
    print(f"  S²/m <= 2d_eff (CS valid): {cs_valid}/{len(data)}; CS enough (2d_eff<=d_eff+1-λ): {cs_enough}/{len(data)} (expect ~0)")

    print("\n" + "=" * 92)
    print("TASK 3 — centered CS: S² <= fᵀ(D-d̄)²f (valid); enough (<= m(d_eff+1-λ))?")
    print("=" * 92)
    t3_valid = sum(1 for _, q in data if q['t3_cs'] >= -1e-7)
    t3_enough = sum(1 for _, q in data if q['t3_enough'] >= -1e-7)
    print(f"  S² <= fᵀ(D-d̄)²f (CS valid): {t3_valid}/{len(data)}; enough: {t3_enough}/{len(data)}")

    print("\n" + "=" * 92)
    print("tight cases (min target): where is the spectral bound saturated?")
    print("=" * 92)
    for nm, q in sorted(data, key=lambda x: x[1]['target'])[:8]:
        print(f"  {nm:12s} target slack={q['target']:.5f} matrix_min={q['matrix_min']:.4f} "
              f"d_eff={q['d_eff']:.3f} λ={q['lam']:.3f} S²/m={q['S2m']:.3f} {'simple' if q['simple'] else 'DEGEN'}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  TARGET fᵀAf>=S²/m-1: {ok}/{len(data)} (min {mn[1]['target']:.4f}). "
          f"MATRIX A+I-ddᵀ/m>=0 on 1⊥: {okm}/{len(data)} (min {mnm[1]['matrix_min']:.4f}).")
    print(f"  => {'matrix form CLEAN' if okm==len(data) else 'matrix form fails; need Fiedler eqn'}")


if __name__ == "__main__":
    main()
