"""
Low-rank negative of S = (LD+DL)/2 - L_t. S_ii=d^2-sigma, S_ij=t-(d_i+d_j)/2 (edges), 0 else.
TASK1 neg rank/eigenvectors/localization; TASK2 S=S_+ - sum a_j w_j w_j^T; TASK4 Schur on ports P.
Goal: S_HH PSD + port Schur complement small => aggregate reduces to controllable port obstruction.
Run: python slack_matrix_low_rank_negative.py
"""
import numpy as np
import networkx as nx


def split_ports(d):
    n = len(d); order = np.argsort(d); sd = d[order]
    gaps = [(sd[i + 1] - sd[i], i) for i in range(n - 1)]; gap, idx = max(gaps)
    return set(order[:idx + 1].tolist()) if (gap >= 2 and idx < n - 1) else set()


def analyze(G, name):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L)
    Had = A2 * A; Lt = np.diag(Had.sum(1)) - Had; D = np.diag(d)
    S = (L @ D + D @ L) / 2 - Lt
    sev, svec = np.linalg.eigh(S)
    neg = np.where(sev < -1e-7)[0]; nneg = len(neg)
    # localization of negative eigenvectors + port support
    P = split_ports(d); H = sorted(set(range(n)) - P); Pl = sorted(P)
    port_supp = []
    for j in neg:
        w = svec[:, j]
        port_supp.append(float(sum(w[p] ** 2 for p in P)))
    # TASK4: block / Schur on ports
    SHH_psd = None; schur_neg = None; nP = len(Pl)
    if nP >= 1 and len(H) >= 1:
        SHH = S[np.ix_(H, H)]; SPP = S[np.ix_(Pl, Pl)]; SPH = S[np.ix_(Pl, H)]
        eHH = np.linalg.eigvalsh(SHH)
        SHH_psd = float(eHH[0])  # min eig of core block
        if eHH[0] > 1e-9:
            schur = SPP - SPH @ np.linalg.solve(SHH, SPH.T)
            schur_neg = int((np.linalg.eigvalsh(schur) < -1e-7).sum())
    # TASK2: S_+ = S + sum a_j w_j w_j^T (lift negatives to 0); test u_k^T S_+ u_k >= sum a_j <u_k,w_j>^2
    Splus = S.copy()
    for j in neg:
        Splus = Splus + (-sev[j]) * np.outer(svec[:, j], svec[:, j])
    # u_k^T S_+ u_k >= sum_j (-sev_j) <u_k,w_j>^2  <=> u_k^T S u_k >=0 (identity); verify margin
    decomp_ok = True
    for k in range(n):
        lhs = float(U[:, k] @ Splus @ U[:, k])
        rhs = sum((-sev[j]) * (U[:, k] @ svec[:, j]) ** 2 for j in neg)
        if lhs < rhs - 1e-6: decomp_ok = False
    # max overlap of any Laplacian eigenvector with negative eigenspace
    maxov = 0.0
    for k in range(n):
        ov = sum((U[:, k] @ svec[:, j]) ** 2 for j in neg)
        maxov = max(maxov, ov)
    return dict(name=name, n=n, nP=nP, nneg=nneg, minS=float(sev[0]),
                SHH_minei=SHH_psd, schur_neg=schur_neg,
                port_supp=max(port_supp) if port_supp else 0.0, maxov=maxov, decomp_ok=decomp_ok)


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
        for q in [0.2, 0.4, 0.6, 0.9]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    for N in [30, 50, 80]:
        for dd in [2, 3, 4]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for kc, ks in [(10, 6), (12, 8)]: out.append((f"star{kc}_{ks}", star(kc, ks)))
    for k, l in [(10, 10), (15, 12)]: out.append((f"lolli{k}_{l}", nx.lollipop_graph(k, l)))
    for nn in [25, 40]:
        for q in [0.3, 0.6]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G, nm)] if q is not None]

    print("=" * 96)
    print("TASK 1 — negative rank of S; port support of neg eigenvectors; max Laplacian overlap")
    print("=" * 96)
    print(f"  {'graph':12s} {'n':>4} {'#ports':>6} {'#neg S':>7} {'min S':>8} {'neg-vec port supp':>17} {'max |<u,W->|²':>13}")
    for nm, q in sorted(data, key=lambda x: -x[1]['nneg'])[:14]:
        print(f"  {nm:12s} {q['n']:4d} {q['nP']:6d} {q['nneg']:7d} {q['minS']:8.2f} {q['port_supp']:17.3f} {q['maxov']:13.3f}")
    print(f"  max #neg S over corpus = {max(q['nneg'] for _,q in data)}")

    print("\n" + "=" * 96)
    print("TASK 4 — Schur on ports: S_HH PSD? port Schur complement negatives = #neg S?")
    print("=" * 96)
    shh_psd = sum(1 for _, q in data if q['SHH_minei'] is not None and q['SHH_minei'] >= -1e-7)
    valid = [q for _, q in data if q['SHH_minei'] is not None]
    print(f"  S_HH (core block) PSD: {shh_psd}/{len(valid)}")
    print(f"  {'graph':12s} {'#ports':>6} {'S_HH min eig':>13} {'#neg S':>7} {'Schur #neg':>11}")
    for nm, q in sorted(data, key=lambda x: (x[1]['SHH_minei'] if x[1]['SHH_minei'] is not None else 9))[:14]:
        sm = q['SHH_minei']; sn = q['schur_neg']
        print(f"  {nm:12s} {q['nP']:6d} {(sm if sm is not None else float('nan')):13.3f} {q['nneg']:7d} "
              f"{(sn if sn is not None else -1):11d}")
    print("  (S_HH PSD AND Schur #neg == #neg S => negative confined to port Schur complement)")

    print("\n" + "=" * 96)
    print("TASK 2 — decomposition S=S_+ - Σα_j w_j w_j^T; identity check")
    print("=" * 96)
    print(f"  u_k^T S_+ u_k >= Σα_j<u_k,w_j>² (= u_k^T S u_k>=0) holds: "
          f"{sum(1 for _,q in data if q['decomp_ok'])}/{len(data)}")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  max #neg S = {max(q['nneg'] for _,q in data)}; S_HH PSD: {shh_psd}/{len(valid)}; "
          f"max Laplacian overlap with N-(S) = {max(q['maxov'] for _,q in data):.3f}")
    schur_match = sum(1 for q in valid if q['SHH_minei'] >= -1e-7 and q['schur_neg'] == q['nneg'])
    print(f"  S_HH PSD AND Schur #neg matches #neg S: {schur_match}/{len(valid)} "
          f"=> negative localized to port Schur complement")


if __name__ == "__main__":
    main()
