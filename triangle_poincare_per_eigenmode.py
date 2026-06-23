"""
Per-eigenmode triangle Poincare: u_k^T L_t u_k <= lam_k * u_k^T D u_k for EVERY Laplacian eigenpair.
C_k = u_k^T L_t u_k / (lam_k u_k^T D u_k). Fiedler (k=2) = aggregate_triangle_poincare.
Test all modes; arbitrary-vector C vs eigenvector C (TASK4); failing modes (TASK5).
Run: python triangle_poincare_per_eigenmode.py
"""
import numpy as np
import networkx as nx


def build(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L)
    Had = A2 * A; Lt = np.diag(Had.sum(1)) - Had; D = np.diag(d)
    return n, A, d, L, ev, U, Lt, D


def analyze(G, name):
    n, A, d, L, ev, U, Lt, D = build(G)
    lam2 = ev[1]
    Ck = []; ks = []
    for k in range(n):
        if ev[k] <= 1e-9: continue
        u = U[:, k]
        uLt = float(u @ Lt @ u); uD = float(u @ D @ u)
        if uD > 1e-12:
            Ck.append(uLt / (ev[k] * uD)); ks.append(k)
    Ck = np.array(Ck); ks = np.array(ks)
    kmax = ks[int(np.argmax(Ck))]
    # arbitrary-vector C (random) for the cubic form (TASK4)
    rng = np.random.default_rng(0); Crand = 0.0
    for _ in range(300):
        v = rng.standard_normal(n)
        num = float(v @ Lt @ v) * float(v @ v); den = float(v @ L @ v) * float(v @ D @ v)
        if den > 1e-9 and num > 0: Crand = max(Crand, num / den)
    # which part of spectrum is the max mode (rank fraction)
    return dict(name=name, n=n, maxC=float(Ck.max()), kmax=int(kmax), lam_kmax=float(ev[kmax]),
                lam2=lam2, ev_max=float(ev[-1]), C_fiedler=float(Ck[0]) if ks[0] == 1 else None,
                kfrac=float(np.where(ks == kmax)[0][0]) / len(ks), Crand=Crand,
                nfail=int((Ck > 1 + 1e-7).sum()))


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
    for nn in [30, 50, 80]:
        for q in [0.1, 0.3, 0.6, 0.9]: out.append((f"deg2d{nn}_{q}", "TYPEA", d2(nn, q, 7)))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", "TYPEA", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", "CLIQUESTAR", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", "TYPEB", nx.lollipop_graph(k, l)))
    for k, l in [(8, 8)]: out.append((f"barb{k}_{l}", "TYPEB", nx.barbell_graph(k, l)))
    for nn in [25, 40, 60]:
        for q in [0.2, 0.4, 0.7]: out.append((f"gnp{nn}_{q}", "RANDOM", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20, 40]:
        for r in [4, nn // 2]:
            if 3 <= r < nn and (r * nn) % 2 == 0: out.append((f"rr{nn}_{r}", "REGULAR", nx.random_regular_graph(r, nn, seed=1)))
    out.append(("cocktail6", "MULTIPART", nx.complete_multipartite_graph(*([2] * 6))))
    out.append(("Kmp345", "MULTIPART", nx.complete_multipartite_graph(3, 4, 5)))
    for nn in [12, 20, 30]: out.append((f"K{nn}", "REGULAR", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, cl, q) for nm, cl, G in corpus() for q in [analyze(G, nm)] if q is not None]

    print("=" * 100)
    print("TASK 1 — per-eigenmode C_k = u^T L_t u/(λ_k u^T D u) for ALL modes; max_k C_k <= 1?")
    print("=" * 100)
    allok = sum(1 for _, _, q in data if q['nfail'] == 0)
    print(f"  max_k C_k <= 1 (per-mode Poincare holds for ALL modes): {allok}/{len(data)}")
    print(f"  {'graph':12s} {'class':>11} {'max_k C_k':>9} {'k_max':>6} {'λ_kmax':>8} {'λ2':>6} {'spectrum frac':>13}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['maxC'])[:14]:
        print(f"  {nm:12s} {cl:>11} {q['maxC']:9.4f} {q['kmax']:6d} {q['lam_kmax']:8.2f} {q['lam2']:6.2f} {q['kfrac']:13.2f}")

    print("\n" + "=" * 100)
    print("TASK 5 — failing modes (C_k > 1)?")
    print("=" * 100)
    fails = [(nm, cl, q) for nm, cl, q in data if q['nfail'] > 0]
    if fails:
        for nm, cl, q in fails:
            print(f"  {nm:12s} ({cl}) #modes with C_k>1: {q['nfail']}, max C_k = {q['maxC']:.4f} at k={q['kmax']}")
    else:
        print("  NONE — per-eigenmode Poincare holds for EVERY mode on the corpus.")

    print("\n" + "=" * 100)
    print("TASK 4 — eigenvector C (max_k C_k) vs arbitrary-vector C (cubic form, random v)")
    print("=" * 100)
    print(f"  {'graph':12s} {'eigen max_k C_k':>15} {'arbitrary-v C':>14} {'gap (arb-eigen)':>16}")
    for nm, cl, q in sorted(data, key=lambda x: -x[2]['Crand'])[:10]:
        print(f"  {nm:12s} {q['maxC']:15.4f} {q['Crand']:14.4f} {q['Crand']-q['maxC']:16.4f}")
    print("  (arbitrary-v C > 1 while eigenvector C <= 1 => eigenvector structure essential)")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    gmax = max(data, key=lambda x: x[2]['maxC'])
    print(f"  per-eigenmode Poincare (max_k C_k<=1): {allok}/{len(data)}; "
          f"global max_k C_k = {gmax[2]['maxC']:.4f} at {gmax[0]} (k={gmax[2]['kmax']})")
    print(f"  arbitrary-v C max = {max(q['Crand'] for _,_,q in data):.4f} (>1 => eigenvector-specific)")


if __name__ == "__main__":
    main()
