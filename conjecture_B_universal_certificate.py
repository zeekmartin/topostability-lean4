"""
Is the S-procedure constant c universally bounded? Certificate Q + 2cL(L-lam I) >= 0, M=cL.
Per-mode (diagonal in L-basis): c_k = max(0, -q_k/(2 lam_k(lam_k-lam))), q_k=u_k^T Q u_k.
NB Q does NOT commute with L => diagonal c_required is a LOWER bound; actual c_PSD from full scan.
Per-mode Poincare: C = max_k u_k^T L_t u_k/(lam_k u_k^T D u_k). Test growth with n, Delta.
Run: python conjecture_B_universal_certificate.py
"""
import numpy as np
import networkx as nx


def build(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A; A2 = A @ A
    ev, U = np.linalg.eigh(L); lam = ev[1]
    Had = A2 * A; Lt = np.diag(Had.sum(1)) - Had; D = np.diag(d)
    Q = lam * D - Lt
    return n, A, d, L, ev, U, lam, Lt, D, Q


def analyze(G, name):
    n, A, d, L, ev, U, lam, Lt, D, Q = build(G)
    Delta = int(d.max())
    # per-mode diagonal q_k and required c (modes with lam_k>lam)
    qk = np.array([float(U[:, k] @ Q @ U[:, k]) for k in range(n)])
    lamk = ev
    c_req = 0.0; c_arg = -1
    for k in range(n):
        lift = 2 * lamk[k] * (lamk[k] - lam)
        if lift > 1e-9 and qk[k] < 0:
            ck = -qk[k] / lift
            if ck > c_req: c_req = ck; c_arg = k
    # per-mode Poincare C = max_{k>=2} (u^T L_t u)/(lam_k u^T D u)
    Cpoin = 0.0
    for k in range(n):
        if lamk[k] > lam + 1e-9:
            uLt = float(U[:, k] @ Lt @ U[:, k]); uD = float(U[:, k] @ D @ U[:, k])
            if uD > 1e-12 and lamk[k] > 1e-9:
                Cpoin = max(Cpoin, uLt / (lamk[k] * uD))
    # actual c_PSD: smallest c making Q+2cL(L-lam I)>=0 (bisection on min-eig)
    LL = 2 * (L @ L) - 2 * lam * L
    def mineig(c): return float(np.linalg.eigvalsh(Q + c * LL)[0])
    lo, hi = 0.0, 1.0
    while mineig(hi) < 0 and hi < 1e8: hi *= 2
    for _ in range(40):
        mid = (lo + hi) / 2
        if mineig(mid) >= -1e-7: hi = mid
        else: lo = mid
    c_psd = hi
    # growth indicators for q_k vs lam_k (high modes)
    return dict(name=name, n=n, Delta=Delta, lam=lam, c_req=c_req, c_psd=c_psd, Cpoin=Cpoin,
                ev_max=ev[-1], qk=qk, lamk=lamk)


def main():
    def d2(nn, q, s):
        H = nx.gnp_random_graph(nn - 1, q, seed=s); H.add_node(nn - 1); H.add_edge(nn - 1, 0); H.add_edge(nn - 1, 1); return H
    def twin(N, dd):
        K = nx.complete_graph(N); a, b = N, N + 1
        for x in (a, b):
            for w in range(dd): K.add_edge(x, w)
        K.add_node(N + 2); K.add_edge(N + 2, a); K.add_edge(N + 2, b); return K
    # increasing size to detect growth
    fam = []
    for N in [20, 40, 80, 160]: fam.append((f"K{N}", nx.complete_graph(N)))
    for nn in [40, 80, 160, 240]: fam.append((f"deg2d{nn}_0.6", d2(nn, 0.6, 7)))
    for N in [20, 40, 80, 140]: fam.append((f"twin{N}_2", twin(N, 2)))
    for nn in [30, 60, 120]: fam.append((f"gnp{nn}_0.5", nx.gnp_random_graph(nn, 0.5, seed=3)))
    res = [analyze(G, nm) for nm, G in fam]

    print("=" * 96)
    print("TASK 1/5 — required c (diagonal lower bd) and actual c_PSD; growth with n, Δ?")
    print("=" * 96)
    print(f"  {'graph':14s} {'n':>5} {'Δ':>5} {'ev_max':>7} {'c_req(diag)':>11} {'c_PSD(full)':>11} {'c_PSD/Δ':>8} {'c_PSD/n':>8}")
    for q in res:
        print(f"  {q['name']:14s} {q['n']:5d} {q['Delta']:5d} {q['ev_max']:7.1f} {q['c_req']:11.2f} "
              f"{q['c_psd']:11.2f} {q['c_psd']/q['Delta']:8.3f} {q['c_psd']/q['n']:8.3f}")

    print("\n" + "=" * 96)
    print("TASK 4 — per-mode Poincare C = max_k u^T L_t u/(λ_k u^T D u); growth?")
    print("=" * 96)
    print(f"  {'graph':14s} {'n':>5} {'Δ':>5} {'C_poincare':>11} {'C/Δ':>7}")
    for q in res:
        print(f"  {q['name']:14s} {q['n']:5d} {q['Delta']:5d} {q['Cpoin']:11.2f} {q['Cpoin']/q['Delta']:7.3f}")

    print("\n" + "=" * 96)
    print("TASK 2 — growth of c_PSD with n within each family (slope on log-log)")
    print("=" * 96)
    import re
    fams = {}
    for q in res:
        key = re.sub(r'\d+', '#', q['name'])
        fams.setdefault(key, []).append((q['n'], q['c_psd'], q['Delta']))
    for key, pts in fams.items():
        pts = sorted(pts)
        ns = np.array([p[0] for p in pts]); cs = np.array([max(p[1], 1e-6) for p in pts])
        if len(pts) >= 2 and cs.min() > 0:
            slope_n = np.polyfit(np.log(ns), np.log(cs), 1)[0]
            print(f"  {key:16s} c_PSD: {['%.1f'%p[1] for p in pts]}  d log c/d log n ≈ {slope_n:.2f}")

    print("\n" + "=" * 96)
    print("SUMMARY")
    print("=" * 96)
    maxc = max(q['c_psd'] for q in res)
    print(f"  max c_PSD over corpus = {maxc:.1f} (at largest graphs)")
    print(f"  c_PSD/Δ range [{min(q['c_psd']/q['Delta'] for q in res):.3f}, {max(q['c_psd']/q['Delta'] for q in res):.3f}]")
    print(f"  c_PSD/n  range [{min(q['c_psd']/q['n'] for q in res):.3f}, {max(q['c_psd']/q['n'] for q in res):.3f}]")
    print("  => if c_PSD/Δ or c_PSD/n roughly CONSTANT: c grows linearly (NOT universally bounded).")
    print("     if c_PSD itself plateaus: BOUNDED (universal certificate exists).")


if __name__ == "__main__":
    main()
