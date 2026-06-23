"""
L_t in the Laplacian eigenbasis. B=U^T L_t U, H=U^T D U. Target B_kk <= lam_k H_kk.
Since U^T L = Lam U^T: lam_k H_kk = (U^T (LD+DL)/2 U)_kk. So define lambda-FREE matrix
  S = (LD+DL)/2 - L_t,  with u_k^T S u_k = lam_k H_kk - B_kk (per-mode slack) for EVERY mode.
Structure: S supported on diag + edges; S_ii=d_i^2-sigma_i, S_ij=t_ij-(d_i+d_j)/2 on edges, 0 else.
Aggregate <=> S >= 0 on eigenspaces. Test if S globally PSD (Schur).
Run: python triangle_poincare_eigenbasis_diagonal.py
"""
import numpy as np
import networkx as nx


def build(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L)
    Had = A2 * A; Lt = np.diag(Had.sum(1)) - Had; D = np.diag(d)
    return n, A, d, L, ev, U, Lt, D, A2


def analyze(G, name):
    n, A, d, L, ev, U, Lt, D, A2 = build(G)
    B = U.T @ Lt @ U; H = U.T @ D @ U
    # diagonal ratio B_kk/(lam_k H_kk), modes with lam_k>0
    ratios = []
    for k in range(n):
        if ev[k] > 1e-9 and H[k, k] > 1e-12:
            ratios.append(B[k, k] / (ev[k] * H[k, k]))
    ratios = np.array(ratios)
    # off-diagonal magnitudes (Frobenius)
    offB = np.sqrt((B ** 2).sum() - (np.diag(B) ** 2).sum())
    diagB = np.sqrt((np.diag(B) ** 2).sum())
    # lambda-free S = (LD+DL)/2 - L_t
    S = (L @ D + D @ L) / 2 - Lt
    Sev = np.linalg.eigvalsh(S)
    # verify S structure: S_ii=d^2-sigma, S_ij=t-(d_i+d_j)/2 on edges, 0 non-edges
    sigma = (A2 * A).sum(1)
    Sdiag_pred = d ** 2 - sigma
    err_diag = float(np.max(np.abs(np.diag(S) - Sdiag_pred)))
    err_edge = 0.0; err_none = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            if A[i, j] > 0:
                err_edge = max(err_edge, abs(S[i, j] - (A2[i, j] - (d[i] + d[j]) / 2)))
            else:
                err_none = max(err_none, abs(S[i, j]))
    # verify u_k^T S u_k = lam_k H_kk - B_kk
    err_slack = max(abs(float(U[:, k] @ S @ U[:, k]) - (ev[k] * H[k, k] - B[k, k])) for k in range(n))
    # diagonal dominance: d_i^2 >= s_i ? (s_i = neighbor degree sum)
    s = A @ d
    dd_fail = int((d ** 2 < s - 1e-9).sum())
    return dict(name=name, n=n, maxratio=float(ratios.max()), off_over_diag=offB / max(diagB, 1e-12),
                minS=float(Sev[0]), nnegS=int((Sev < -1e-7).sum()),
                err_diag=err_diag, err_edge=err_edge, err_none=err_none, err_slack=err_slack,
                dd_fail=dd_fail)


def corpus():
    out = []; rng = np.random.default_rng(0)
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    for nn in [40, 60]:
        for q in [0.2, 0.6, 0.9]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    for N in [30, 50]:
        for dd in [2, 3]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for nn in [25, 40]:
        for q in [0.3, 0.6]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    out.append(("lolli15_12", nx.lollipop_graph(15, 12)))
    out.append(("cocktail6", nx.complete_multipartite_graph(*([2] * 6))))
    for nn in [12, 20]: out.append((f"K{nn}", nx.complete_graph(nn)))
    for nn in [20]: out.append((f"rr{nn}_6", nx.random_regular_graph(6, nn, seed=1)))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G, nm)] if q is not None]

    print("=" * 96)
    print("TASK 2/4 — lambda-free S=(LD+DL)/2-L_t: structure + slack identity (max errors)")
    print("=" * 96)
    print(f"  S_ii = d_i²-σ_i           : max err {max(q['err_diag'] for _,q in data):.1e}")
    print(f"  S_ij = t_ij-(d_i+d_j)/2 (edges) : max err {max(q['err_edge'] for _,q in data):.1e}")
    print(f"  S_ij = 0 (non-edges)      : max err {max(q['err_none'] for _,q in data):.1e}")
    print(f"  u_k^T S u_k = λ_k H_kk - B_kk : max err {max(q['err_slack'] for _,q in data):.1e}")

    print("\n" + "=" * 96)
    print("TASK 1 — diagonal ratio (per-mode Poincare) and off-diagonal magnitude in L-basis")
    print("=" * 96)
    print(f"  {'graph':12s} {'max B_kk/(λ_k H_kk)':>19} {'||off B||/||diag B||':>20}")
    for nm, q in sorted(data, key=lambda x: -x[1]['maxratio'])[:10]:
        print(f"  {nm:12s} {q['maxratio']:19.4f} {q['off_over_diag']:20.3f}")
    print("  (diag ratio <=1 = per-mode holds; large off/diag => arbitrary-v violations come from off-diag)")

    print("\n" + "=" * 96)
    print("TASK 4 — is S = (LD+DL)/2 - L_t GLOBALLY PSD? (Schur mechanism)")
    print("=" * 96)
    psd = sum(1 for _, q in data if q['minS'] >= -1e-7)
    print(f"  S ⪰ 0 globally: {psd}/{len(data)}")
    print(f"  {'graph':12s} {'min eig S':>10} {'#neg S':>7} {'diag-dominance fails (#v: d²<s)':>32}")
    for nm, q in sorted(data, key=lambda x: x[1]['minS'])[:10]:
        print(f"  {nm:12s} {q['minS']:10.3f} {q['nnegS']:7d} {q['dd_fail']:32d}")
    print("  (S_ij<0 on edges [t<avg deg], S_ii=d²-σ>0; diag-dominance d²>=s fails at low-deg ports)")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    print(f"  per-mode diag ratio <=1: {sum(1 for _,q in data if q['maxratio']<=1+1e-7)}/{len(data)}")
    print(f"  S globally PSD: {psd}/{len(data)} (min eig over corpus {min(q['minS'] for _,q in data):.2f})")
    print(f"  => S indefinite (off-diagonal) => aggregate is S⪰0 on EIGENSPACES, not global; "
          f"λ-free reformulation of Q.")


if __name__ == "__main__":
    main()
