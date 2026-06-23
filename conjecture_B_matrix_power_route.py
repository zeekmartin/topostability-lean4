"""
Matrix-power route for T. T_unord = f^T L_t f = Sum_v sigma_v f_v^2 - f^T(A^2 o A)f.
Identities to test: f^T A^2 f = Sum(d_v-lam)^2 f_v^2; (A^3)_vv = sigma_v; f^T A^3 f.
Question: does T reduce to {f^T A^k f, Sum d^k f^2, Sum d^k f, lam}? (Hadamard A^2 o A obstruction.)
Run: python conjecture_B_matrix_power_route.py
"""
import numpy as np
import networkx as nx


def analyze(G):
    G = nx.convert_node_labels_to_integers(G); n = G.number_of_nodes()
    if not nx.is_connected(G): return None
    A = nx.to_numpy_array(G); d = A.sum(1); L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    A2 = A @ A; A3 = A2 @ A
    Had = A2 * A                         # A^2 o A (Hadamard, t_e on edges)
    sigma = Had.sum(1)                   # row sums = triangle degree = (A^3)_vv
    Lt = np.diag(sigma) - Had
    edges = [(i, j) for i in range(n) for j in range(i + 1, n) if A[i, j] > 0]
    T = sum(A2[a, b] * (f[a] - f[b]) ** 2 for a, b in edges)         # T_unord
    # matrix forms
    fLt = float(f @ Lt @ f)              # = T_unord
    fA2 = float(f @ A2 @ f); fA3 = float(f @ A3 @ f)
    fHad = float(f @ Had @ f)
    sig_f2 = float(sigma @ (f * f))
    # known: f^T A^2 f = Sum(d-lam)^2 f^2
    pred_A2 = float(((d - lam) ** 2 * (f * f)).sum())
    # (A^3)_vv = sigma_v ?
    diagA3 = np.diag(A3)
    id_diag = float(np.max(np.abs(diagA3 - sigma)))
    # degree-power sums
    Sf = float((f * f).sum())            # =1
    d1f2 = float((d * f * f).sum()); d2f2 = float((d * d * f * f).sum())
    d3f2 = float((d ** 3 * f * f).sum())
    return dict(n=n, lam=lam, T=T, fLt=fLt, fA2=fA2, fA3=fA3, fHad=fHad, sig_f2=sig_f2,
                pred_A2=pred_A2, id_diag=id_diag,
                id_T=abs(T - (sig_f2 - fHad)),          # T = Sum sigma f^2 - f^T Had f
                id_A2=abs(fA2 - pred_A2),               # f^T A^2 f = Sum(d-lam)^2 f^2
                d_eff=d1f2, d2f2=d2f2, d3f2=d3f2)


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
        for q in [0.1, 0.3, 0.6, 0.9]: out.append((f"deg2d{nn}_{q}", d2(nn, q, 7)))
    for N in [30, 50]:
        for dd in [2, 3]: out.append((f"twin{N}_{dd}", twin(N, dd)))
    for nn in [25, 40]:
        for q in [0.3, 0.6]: out.append((f"gnp{nn}_{q}", nx.gnp_random_graph(nn, q, seed=int(rng.integers(1e9)))))
    for nn in [20]:
        out.append((f"rr{nn}_6", nx.random_regular_graph(6, nn, seed=1)))
    for nn in [12, 20, 30]: out.append((f"K{nn}", nx.complete_graph(nn)))
    return out


def main():
    data = [(nm, q) for nm, G in corpus() for q in [analyze(G)] if q is not None]
    print(f"  {len(data)} graphs")

    print("\n" + "=" * 92)
    print("TASK 1/3 — exact identities")
    print("=" * 92)
    print(f"  T_unord = f^T L_t f                : max err {max(abs(q['T']-q['fLt']) for _,q in data):.2e}")
    print(f"  T = Sum σ_v f² - f^T(A²∘A)f         : max err {max(q['id_T'] for _,q in data):.2e}")
    print(f"  f^T A² f = Σ(d_v-λ)² f²            : max err {max(q['id_A2'] for _,q in data):.2e}")
    print(f"  (A³)_vv = σ_v                       : max err {max(q['id_diag'] for _,q in data):.2e}")

    print("\n" + "=" * 92)
    print("TASK 2/4 — does the Hadamard f^T(A²∘A)f reduce to f^T A^k f / degree sums?")
    print("=" * 92)
    # Test: is f^T(A²∘A)f = a*fA2 + b*fA3 + c*d2f2 + ... for FIXED coeffs across graphs?
    # Build linear system and check residual of least-squares fit (exact => residual 0).
    X = np.array([[q['fA2'], q['fA3'], q['d2f2'], q['d3f2'], q['d_eff'], q['lam'], 1.0] for _, q in data])
    y = np.array([q['fHad'] for _, q in data])
    coef, res, rank, sv = np.linalg.lstsq(X, y, rcond=None)
    pred = X @ coef
    relresid = np.linalg.norm(pred - y) / max(np.linalg.norm(y), 1e-9)
    print(f"  best linear fit f^T(A²∘A)f ~ [fA2,fA3,d²f²,d³f²,d_eff,λ,1]: rel residual = {relresid:.4f}")
    print(f"  (≈0 => reduces to matrix powers/degree sums; >>0 => Hadamard IRREDUCIBLE)")
    # same for T and sig_f2
    yT = np.array([q['T'] for _, q in data])
    cT, _, _, _ = np.linalg.lstsq(X, yT, rcond=None)
    print(f"  best linear fit T ~ same basis: rel residual = {np.linalg.norm(X@cT-yT)/np.linalg.norm(yT):.4f}")
    ysig = np.array([q['sig_f2'] for _, q in data])
    csig, _, _, _ = np.linalg.lstsq(X, ysig, rcond=None)
    print(f"  best linear fit Σσf² ~ same basis: rel residual = {np.linalg.norm(X@csig-ysig)/np.linalg.norm(ysig):.4f}")

    print("\n" + "=" * 92)
    print("TASK 5 — is f^T A² f or f^T A³ f related to T ≤ 2λ·d_eff usefully?")
    print("=" * 92)
    print(f"  {'graph':12s} {'T':>9} {'2λd_eff':>9} {'fA2':>9} {'fA3':>9} {'Σσf²':>9}")
    for nm, q in sorted(data, key=lambda x: -x[1]['T'] / (2 * x[1]['lam'] * x[1]['d_eff']))[:8]:
        print(f"  {nm:12s} {q['T']:9.3f} {2*q['lam']*q['d_eff']:9.3f} {q['fA2']:9.3f} {q['fA3']:9.3f} {q['sig_f2']:9.3f}")

    print("\n" + "=" * 92)
    print("SUMMARY")
    print("=" * 92)
    print(f"  identities exact. Hadamard f^T(A²∘A)f rel-residual vs matrix-power basis = {relresid:.3f}")
    print(f"  => {'REDUCIBLE' if relresid<0.01 else 'IRREDUCIBLE (Hadamard not a polynomial in A)'}")


if __name__ == "__main__":
    main()
