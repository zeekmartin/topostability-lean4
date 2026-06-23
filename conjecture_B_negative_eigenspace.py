"""
Negative eigenspace of Q = lam*D - L_t. What ARE the negative directions?
TASK1 localization; TASK2 frequency content + Q'=Q+2L^2-2lam*L (M=L certificate); TASK3 angle(f,N-);
TASK4 structural pattern.
Run: python conjecture_B_negative_eigenspace.py
"""
import numpy as np
import networkx as nx


def build(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    Had = A2 * A; Lt = np.diag(Had.sum(1)) - Had; D = np.diag(d)
    Q = lam * D - Lt
    return dict(n=n, A=A, d=d, L=L, ev=ev, U=U, lam=lam, f=f, Lt=Lt, D=D, Q=Q, A2=A2)


def analyze(G, name):
    B = build(G); n = B['n']; Q = B['Q']; f = B['f']; L = B['L']; lam = B['lam']
    ev, U, d, A2, A = B['ev'], B['U'], B['d'], B['A2'], B['A']
    qev, qvec = np.linalg.eigh(Q)
    neg = np.where(qev < -1e-7)[0]
    nneg = len(neg)
    # TASK 1: localization of negative eigenvectors
    pr = []; freq = []; core_conc = []
    dmax = d.max()
    for k in neg:
        v = qvec[:, k]
        pr.append(1.0 / float((v ** 4).sum()))                  # participation ratio (n=spread,1=localized)
        freq.append(float(v @ L @ v) / float(v @ v))            # Rayleigh (Laplacian) = frequency
        # concentration on high-degree (dense-core) vertices: weight on top-25% degree
        thr = np.percentile(d, 75)
        core_conc.append(float((v[d >= thr] ** 2).sum()))
    # TASK 3: angle f vs negative eigenspace
    if nneg:
        Vn = qvec[:, neg]
        overlap = float(np.linalg.norm(Vn.T @ f))               # ||proj of f onto N-||
        angle = np.degrees(np.arccos(min(1.0, np.sqrt(max(0.0, 1 - overlap ** 2)))))  # angle from N-^perp...
        ang_to_Nperp = np.degrees(np.arcsin(min(1.0, overlap)))  # angle between f and N- (small overlap=>~0 in N-)
    else:
        overlap = 0.0; ang_to_Nperp = 90.0
    # TASK 2: Q' = Q + 2L^2 - 2 lam L (M=L)
    Qp = Q + 2 * (L @ L) - 2 * lam * L
    qpev = np.linalg.eigvalsh(Qp)
    # also M=cL optimal-ish c: scan
    bestc = None
    for c in [0.5, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512]:
        Qc = Q + c * (2 * (L @ L) - 2 * lam * L)
        me = np.linalg.eigvalsh(Qc)[0]
        if bestc is None or me > bestc[1]: bestc = (c, me)
    fQf = float(f @ Q @ f)
    return dict(name=name, n=n, nneg=nneg, minQ=qev[0], fQf=fQf,
                pr_mean=np.mean(pr) if pr else 0, pr_min=np.min(pr) if pr else 0,
                freq_mean=np.mean(freq) if freq else 0, lam=lam, ev_max=ev[-1], ev_med=np.median(ev),
                core_conc=np.mean(core_conc) if core_conc else 0,
                overlap_fN=overlap, ang=ang_to_Nperp,
                minQp=qpev[0], nneg_Qp=int((qpev < -1e-7).sum()),
                bestc=bestc[0], bestc_mineig=bestc[1])


def main():
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    reps = [("rr20_6", nx.random_regular_graph(6, 20, seed=1)),
            ("deg2d40_0.6", d2(40, 0.6, 7)), ("deg2d40_0.2", d2(40, 0.2, 7)),
            ("twin30_2", twin(30, 2)), ("twin50_3", twin(50, 3)),
            ("lolli15_12", nx.lollipop_graph(15, 12)), ("gnp30_0.5", nx.gnp_random_graph(30, 0.5, seed=3)),
            ("gnp40_0.3", nx.gnp_random_graph(40, 0.3, seed=5))]
    res = [analyze(G, nm) for nm, G in reps]

    print("=" * 100)
    print("TASK 1 — localization of Q's negative eigenvectors (PR: n=spread,1=localized; core_conc=mass on top-25% deg)")
    print("=" * 100)
    print(f"  {'graph':12s} {'n':>4} {'#neg':>5} {'PR_mean':>8} {'PR/n':>6} {'core_conc':>10}")
    for q in res:
        print(f"  {q['name']:12s} {q['n']:4d} {q['nneg']:5d} {q['pr_mean']:8.2f} {q['pr_mean']/q['n']:6.2f} {q['core_conc']:10.3f}")
    print("  (PR/n near 1 => delocalized; core_conc near 1 => negatives live on dense-core vertices)")

    print("\n" + "=" * 100)
    print("TASK 2 — frequency of negatives + Q'=Q+2L²-2λL (M=L). Are negatives HIGH-frequency?")
    print("=" * 100)
    print(f"  {'graph':12s} {'freq(neg)':>9} {'λ':>7} {'ev_med':>7} {'ev_max':>7} {'minQ':>8} {'minQ(M=L)':>9} {'#neg(M=L)':>9}")
    for q in res:
        print(f"  {q['name']:12s} {q['freq_mean']:9.2f} {q['lam']:7.2f} {q['ev_med']:7.2f} {q['ev_max']:7.2f} "
              f"{q['minQ']:8.2f} {q['minQp']:9.2f} {q['nneg_Qp']:9d}")
    print("  (freq(neg) >> λ => negatives are high-frequency; minQ(M=L)>=0 => M=L certificate works)")

    print("\n" + "=" * 100)
    print("TASK 2b — best c in M=cL: min-eig of Q + c(2L²-2λL)")
    print("=" * 100)
    print(f"  {'graph':12s} {'best c':>7} {'min-eig':>9} {'fQf':>8} {'cert?':>6}")
    for q in res:
        print(f"  {q['name']:12s} {q['bestc']:7.0f} {q['bestc_mineig']:9.3f} {q['fQf']:8.3f} "
              f"{'YES' if q['bestc_mineig']>=-1e-4 else 'no':>6}")

    print("\n" + "=" * 100)
    print("TASK 3 — angle(f, N₋): overlap of Fiedler with negative eigenspace")
    print("=" * 100)
    print(f"  {'graph':12s} {'||proj_N- f||':>13} {'angle into N₋ (deg)':>20}")
    for q in res:
        print(f"  {q['name']:12s} {q['overlap_fN']:13.2e} {q['ang']:20.3f}")

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print(f"  negatives high-freq: freq(neg)/λ mean = {np.mean([q['freq_mean']/q['lam'] for q in res]):.1f}")
    ml = sum(1 for q in res if q['minQp'] >= -1e-4)
    print(f"  M=L (c=1) certificate Q'⪰0: {ml}/{len(res)}; best M=cL certificate: "
          f"{sum(1 for q in res if q['bestc_mineig']>=-1e-4)}/{len(res)}")
    print(f"  Fiedler overlap with N₋: max {max(q['overlap_fN'] for q in res):.2e}")


if __name__ == "__main__":
    main()
