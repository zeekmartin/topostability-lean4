"""
Structured spectral multipliers for the S-procedure  M + Lambda(L-l)+(L-l)Lambda >= 0 on 1-perp.
(l := lam2, M = lam2(D+A)-(lam2/m)dd^T - L_min,  gap=f^TMf>=0, M1=0, (L-l)f=0.)

Eigenbasis u_1=1(ev0), u_2=f(ev=l), u_3..u_n (ev_k>l). f-coupling b_k = f^T M u_k (k>=3).
ANY Lambda commuting with L (scalar, poly(L), (L-l)^+) annihilates f in the anticommutator
=> cannot change b_k (the f-row); only fixes the u-block. Non-commuting Lambda (diag, decoupling)
can cancel b_k.

Families:
  A. spectral   Lambda = c (L-l)^+   => M' = M + 2c*Pi  (Pi=projector onto u3..un)
  B. decoupling Lambda_dec : Lambda_dec f = -(L-l)^+ M f  (rank<=2(n-2), cancels b_k exactly)
                then M' = blockdiag(gap, M_uu); add c(L-l)^+ to make M_uu PSD.
  C. diagonal   Lambda = diag(beta) (vertex space) - can fix b_k; test structured beta.
  D. polynomial Lambda = aI+bL+cL^2 (commutes with L) - cannot fix b_k (= scalar class).

Report minimal multiplier SIZE (op-norm) and scaling on deg2+dense; spectral gap lam3-lam2.
Run: python conjecture_B_structured_dual_certificate.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques
from conjecture_B_B2prime_scaling import deg2_dense


def build(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1)
    L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges()
    Wmin = np.zeros((n, n))
    for a, b in [(idx[u], idx[v]) for u, v in G.edges()]:
        w = min(d[a], d[b]) - 1; Wmin[a, b] = w; Wmin[b, a] = w
    L_min = np.diag(Wmin.sum(1)) - Wmin
    M = lam * (np.diag(d) + A) - (lam / m) * np.outer(d, d) - L_min
    P = np.eye(n) - np.ones((n, n)) / n
    wp, Vp = np.linalg.eigh(P); B = Vp[:, wp > 0.5]
    gap = float(f @ M @ f)
    LmI = L - lam * np.eye(n)
    # pseudoinverse of (L-l) on span{u3..un}
    tol = 1e-7 * max(1.0, ev[-1])
    Lpinv = np.zeros((n, n)); Pi = np.zeros((n, n))
    for k in range(n):
        if ev[k] - lam > tol:
            uk = U[:, k:k + 1]
            Lpinv += (uk @ uk.T) / (ev[k] - lam)
            Pi += uk @ uk.T
    lam3 = next((ev[k] for k in range(2, n) if ev[k] - lam > tol), lam)
    return dict(n=n, m=m, lam=lam, d=d, f=f, U=U, ev=ev, L=L, M=M, LmI=LmI, B=B, gap=gap,
                Lpinv=Lpinv, Pi=Pi, lam3=lam3, dmax=float(d.max()))


def mineig(q, Mp):
    return float(np.linalg.eigvalsh(q['B'].T @ Mp @ q['B'])[0])


def cstar_spectral(q):
    """min c with M + 2c*Pi PSD on 1-perp."""
    Mp = lambda c: q['M'] + 2 * c * q['Pi']
    if mineig(q, Mp(0)) >= -1e-9:
        return 0.0
    hi = 1.0
    while mineig(q, Mp(hi)) < -1e-9 and hi < 1e12:
        hi *= 2
    lo = 0.0
    for _ in range(60):
        mid = (lo + hi) / 2
        if mineig(q, Mp(mid)) >= -1e-9:
            hi = mid
        else:
            lo = mid
    return hi


def decouple(q):
    """Lambda_dec cancels f-coupling; returns (||Lambda_dec||_2, c* for u-block via +cPi, feasible)."""
    M, U, ev, lam, f = q['M'], q['U'], q['ev'], q['lam'], q['f']
    n = q['n']; tol = 1e-7 * max(1.0, ev[-1])
    Ldec = np.zeros((n, n))
    for k in range(n):
        if ev[k] - lam > tol:
            uk = U[:, k]
            bk = float(f @ M @ uk)
            coeff = -bk / (ev[k] - lam)
            Ldec += coeff * (np.outer(f, uk) + np.outer(uk, f))
    A = q['LmI'] @ Ldec + Ldec @ q['LmI']
    Mdec = M + A                    # should be block-diagonal: f decoupled
    # residual f-coupling (sanity)
    fcoup = float(np.max(np.abs(q['B'].T @ Mdec @ f - (f @ Mdec @ f) * (q['B'].T @ f))))
    # now boost u-block with c*Pi
    Mp = lambda c: Mdec + 2 * c * q['Pi']
    if mineig(q, Mp(0)) >= -1e-9:
        cst = 0.0
    else:
        hi = 1.0
        while mineig(q, Mp(hi)) < -1e-9 and hi < 1e12:
            hi *= 2
        lo = 0.0
        for _ in range(50):
            mid = (lo + hi) / 2
            if mineig(q, Mp(mid)) >= -1e-9:
                hi = mid
            else:
                lo = mid
        cst = hi
    # alternative boost: scalar alpha*(L-l) (eigenvalue-weighted) after decoupling
    Mp2 = lambda a: Mdec + a * q['LmI']
    if mineig(q, Mp2(0)) >= -1e-9:
        cst_sc = 0.0
    else:
        hi = 1.0
        while mineig(q, Mp2(hi)) < -1e-9 and hi < 1e12:
            hi *= 2
        lo = 0.0
        for _ in range(50):
            mid = (lo + hi) / 2
            if mineig(q, Mp2(mid)) >= -1e-9:
                hi = mid
            else:
                lo = mid
        cst_sc = hi
    nrm = float(np.linalg.norm(Ldec, 2))
    feas = mineig(q, Mp(cst)) >= -1e-7
    return nrm, cst, feas, fcoup, cst_sc


def graphs():
    out = []
    for fam, G in ([("corpus", g) for _, g in corpus()]
                   + [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (3, 60))]
                   + [("chain", chain_cliques(mm, k)) for mm, k in ((10, 2), (20, 2), (15, 4))]):
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        ev = np.linalg.eigvalsh(nx.laplacian_matrix(G, nodelist=list(G.nodes()))
                                .toarray().astype(float))
        if ev[1] < 1e-9:
            continue
        out.append(G)
    return out


def main():
    data = [build(G) for G in graphs()]
    ng = len(data)

    print("=" * 78)
    print("A. spectral Lambda=c(L-l)^+  (M+2cPi): does it beat scalar? feasibility + size")
    print("=" * 78)
    cs = [cstar_spectral(q) for q in data]
    print(f"  c* (spectral): min={min(cs):.3f} median={np.median(cs):.3f} max={max(cs):.3f}  "
          f"(feasible {sum(1 for c in cs if c<1e11)}/{ng})")

    print("\n" + "=" * 78)
    print("B. decoupling Lambda_dec (cancel f-coupling) + cPi (boost u-block)")
    print("=" * 78)
    decs = [decouple(q) for q in data]
    fc = max(dd[3] for dd in decs)
    print(f"  max residual f-coupling after decoupling: {fc:.2e} (≈0 => decoupling exact)")
    print(f"  ||Lambda_dec||_2 (f-repair size): median={np.median([dd[0] for dd in decs]):.3f} "
          f"max={max(dd[0] for dd in decs):.3f}")
    print(f"  c* for u-block (after decoupling): median={np.median([dd[1] for dd in decs]):.3f} "
          f"max={max(dd[1] for dd in decs):.3f}")
    print(f"  feasible (M' PSD on 1-perp): {sum(1 for dd in decs if dd[2])}/{ng}")

    print("\n" + "=" * 78)
    print("deg2+dense scaling: which multiplier (if any) stays bounded?")
    print("=" * 78)
    ns = [10, 20, 50, 100, 200]
    rows = []
    print(f"  {'n':>5} {'gap':>9} {'lam3-lam2':>10} {'alpha*scal':>11} {'c*spec':>10} "
          f"{'||Ldec||':>10} {'c*after':>9}")
    for n in ns:
        q = build(deg2_dense(n))
        # scalar alpha*
        Mp = lambda a: q['M'] + a * q['LmI']
        if mineig(q, Mp(0)) >= -1e-9:
            asc = 0.0
        else:
            hi = 1.0
            while mineig(q, Mp(hi)) < -1e-9 and hi < 1e14:
                hi *= 2
            lo = 0.0
            for _ in range(60):
                mid = (lo + hi) / 2
                asc = mid
                if mineig(q, Mp(mid)) >= -1e-9:
                    hi = mid
                else:
                    lo = mid
            asc = hi
        cspec = cstar_spectral(q)
        nrm, cst, feas, _, cst_sc = decouple(q)
        rows.append((n, q['gap'], q['lam3'] - q['lam'], asc, cspec, nrm, cst, cst_sc))
        print(f"  {n:5d} {q['gap']:9.5f} {q['lam3']-q['lam']:10.5f} {asc:11.3f} {cspec:10.3f} "
              f"{nrm:10.3f} {cst:9.3f}  decoup+scalarα={cst_sc:.3f}")
    nsa = np.array([r[0] for r in rows])
    def fit(col, lab):
        ys = np.array([r[col] for r in rows])
        if np.all(ys > 1e-12):
            print(f"    {lab} ~ n^{np.polyfit(np.log(nsa), np.log(ys), 1)[0]:.3f}")
    fit(1, "gap"); fit(2, "lam3-lam2"); fit(3, "alpha*(scalar)")
    fit(4, "c*(spectral)"); fit(5, "||Lambda_dec||"); fit(6, "c*(after decouple,Pi)")
    fit(7, "c*(decouple+scalarα)")

    print("\n" + "=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print("  poly(L)/(L-l)^+ commute with L => cannot fix f-coupling b_k (= scalar class).")
    print("  spectral c(L-l)^+ boosts u-block uniformly (drops the 1/(lam_k-l) factor vs scalar).")
    print("  decoupling Lambda_dec cancels b_k exactly but its size ~ 1/(lam3-lam2) (f-repair).")
    print("  See deg2+dense scaling: bounded multiplier exists iff some column stays ~n^0.")


if __name__ == "__main__":
    main()
