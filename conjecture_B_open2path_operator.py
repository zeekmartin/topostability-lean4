"""
Direct analysis of the open-2-path operator P and Laplacian L_P.

P_ab = #common neighbours of a,b with a != b, a NOT~ b   (open 2-paths / induced cherries)
A^2 = D + M + P   (M = A o A^2 = closed/triangle 2-paths, P = open)
L_P = diag(p) - P,  p_v = sum_b P_vb = sigma_v - d_v - tau_v
Open = f^T L_P f = sum_{a<b} P_ab (f_a-f_b)^2   (manifest sum of squares over open cherries)

aggregate_triangle_poincare  <=>  Open >= sum_v R_v f_v^2 = f^T diag(R) f,
   R_v = (sigma_v - d_v^2) + lam(d_v - lam).
Equivalently f^T (L_P - diag(R)) f = -Q >= 0  (for the Fiedler f only).

TASK1 spectrum of L_P; Open vs lam2(L_P); kernel/projection of f.
TASK2 is L_P - diag(R) PSD? globally / on f-perp-1 / nodal domains / minus neg-R hubs.
TASK3 incidence factorisation L_P = B_open^T B_open, Open = ||B_open f||^2; diag(R) vs Gram.
TASK4 A^2 recursion A^2 f = A D f - lam(D-lam)f projected onto non-edges.
Run: python conjecture_B_open2path_operator.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def graph_quant(fam, G):
    nodes = list(G.nodes())
    n = len(nodes)
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal().copy()
    A = np.diag(d) - L
    ev, V = np.linalg.eigh(L)
    lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    f2 = f * f
    A2 = A @ A
    D = np.diag(d)
    M = A * A2
    P = A2 - D - M
    sigma = A @ d
    pdeg = P.sum(1)
    L_P = np.diag(pdeg) - P
    L_M = np.diag(M.sum(1)) - M
    T = float(f @ L_M @ f)
    Open = float(f @ L_P @ f)
    fDf = float(d @ f2)
    Rvec = (sigma - d ** 2) + lam * (d - lam)
    Q = T - lam * fDf
    return dict(fam=fam, n=n, lam=lam, f=f, f2=f2, d=d, sigma=sigma, A=A, A2=A2, M=M, P=P,
                D=D, L=L, L_P=L_P, L_M=L_M, T=T, Open=Open, fDf=fDf, Rvec=Rvec, Q=Q,
                pdeg=pdeg)


def all_graphs():
    gs = [("corpus", G) for _, G in corpus()]
    gs += [("barbell", nx.barbell_graph(m, Lb)) for m in (5, 20, 40, 80) for Lb in (0, 1, 3)]
    gs += [("glue", glue(a, b)) for a, b in ((5, 5), (20, 20), (40, 40), (3, 60))]
    gs += [("chain", chain_cliques(m, k)) for m, k in ((10, 2), (20, 2), (40, 2), (15, 4))]
    out = []
    for fam, G in gs:
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        ev = np.linalg.eigvalsh(nx.laplacian_matrix(G, nodelist=list(G.nodes()))
                                .toarray().astype(float))
        if ev[1] < 1e-9:
            continue
        out.append((fam, G))
    return out


def main():
    data = [graph_quant(fam, G) for fam, G in all_graphs()]
    ng = len(data)
    print(f"{ng} graphs\n")

    def mx(fn):
        return max(abs(fn(q)) for q in data)

    # ---------------- TASK 1 ----------------
    print("=" * 76)
    print("TASK 1 — spectrum of L_P")
    print("=" * 76)
    kerdim = []; lam2P = []; openOverLam2 = []; lbound_ok = 0; fker = []
    Open_ge_lam2_full = 0
    for q in data:
        w = np.linalg.eigvalsh(q['L_P'])
        kd = int((w < 1e-8).sum())
        kerdim.append(kd)
        nz = w[w >= 1e-8]
        mu = nz.min() if len(nz) else 0.0     # smallest nonzero eigenvalue of L_P
        lam2P.append(mu)
        f = q['f']
        # projection of f onto kernel of L_P
        wv, Vv = np.linalg.eigh(q['L_P'])
        ker = Vv[:, wv < 1e-8]
        proj_ker = ker @ (ker.T @ f)
        fperp = f - proj_ker
        fker.append(float(np.linalg.norm(proj_ker)))
        # Open >= mu * ||fperp||^2 ?
        if q['Open'] >= mu * float(fperp @ fperp) - 1e-7:
            lbound_ok += 1
        if q['Open'] >= mu - 1e-7:     # since ||f||=1 and if ker=span(1), fperp=f
            Open_ge_lam2_full += 1
        openOverLam2.append(q['Open'] / mu if mu > 1e-9 else np.inf)
    kerdim = np.array(kerdim); lam2P = np.array(lam2P); fker = np.array(fker)
    print(f"  ker(L_P) dim = #components of P-graph: =1 (connected) on "
          f"{int((kerdim==1).sum())}/{ng}; >1 on {int((kerdim>1).sum())}")
    print(f"  ||proj_ker(L_P) f|| (f mass in P-kernel): max={fker.max():.4f} "
          f"median={np.median(fker):.4f}")
    print(f"  lam2(L_P) smallest-nonzero: min={lam2P.min():.4f} median={np.median(lam2P):.3f}")
    print(f"  Open >= lam2(L_P)*||f_perp||^2 (spectral lower bnd) : {lbound_ok}/{ng}")
    ratios = np.array([r for r in openOverLam2 if np.isfinite(r)])
    print(f"  Open / lam2(L_P) : min={ratios.min():.3f} median={np.median(ratios):.2f}")
    # correlations
    lamG = np.array([q['lam'] for q in data])
    print(f"  corr(lam2(L_P), lam2(G)) = {np.corrcoef(lam2P, lamG)[0,1]:+.3f}")

    # the spectral route: is sum_v R_v f_v^2 <= lam2(L_P)?  (would give Open>=lam2P>=sumRf2)
    print("\n  --- spectral route test: does lam2(L_P) dominate the demand? ---")
    okA = 0; okB = 0
    for i, q in enumerate(data):
        sumRf2 = float((q['Rvec'] * q['f2']).sum())
        if lam2P[i] >= sumRf2 - 1e-7:
            okA += 1
        if lam2P[i] >= q['Rvec'].max() - 1e-7:
            okB += 1
    print(f"  lam2(L_P) >= sum_v R_v f_v^2  (=> closes via Open>=lam2P): {okA}/{ng}")
    print(f"  lam2(L_P) >= max_v R_v        (stronger)                : {okB}/{ng}")

    # ---------------- TASK 2 ----------------
    print("\n" + "=" * 76)
    print("TASK 2 — is L_P - diag(R) PSD (and on subspaces)?")
    print("=" * 76)
    psd_full = 0; psd_perp = 0; psd_Vp = 0; psd_Vm = 0; psd_nohub = 0
    minfull = []; minperp = []
    fQf_ok = 0
    one = None
    for q in data:
        n = q['n']
        Mop = q['L_P'] - np.diag(q['Rvec'])
        w = np.linalg.eigvalsh(Mop)
        minfull.append(w[0])
        if w[0] >= -1e-7:
            psd_full += 1
        # on f-perp-1 : project out the all-ones vector
        ones = np.ones(n) / np.sqrt(n)
        Pp = np.eye(n) - np.outer(ones, ones)
        Mp = Pp @ Mop @ Pp
        wp = np.linalg.eigvalsh(Mp)
        # smallest eigenvalue on the (n-1)-dim 1-perp space = 2nd smallest of Mp (one ~0 from proj)
        minperp.append(wp[1])
        if wp[1] >= -1e-7:
            psd_perp += 1
        # nodal domains
        for mask, key in [(q['f'] > 0, 'Vp'), (q['f'] < 0, 'Vm')]:
            idx = np.where(mask)[0]
            if len(idx) >= 1:
                sub = Mop[np.ix_(idx, idx)]
                wsub = np.linalg.eigvalsh(sub)
                if wsub[0] >= -1e-7:
                    if key == 'Vp':
                        psd_Vp += 1
                    else:
                        psd_Vm += 1
        # remove negative-R hubs
        keep = np.where(q['Rvec'] >= 0)[0]
        if len(keep) >= 1:
            sub = Mop[np.ix_(keep, keep)]
            wsub = np.linalg.eigvalsh(sub)
            if wsub[0] >= -1e-7:
                psd_nohub += 1
        # the actual conjecture: f^T (L_P - diag R) f = -Q >= 0
        val = float(q['f'] @ Mop @ q['f'])
        if val >= -1e-7:
            fQf_ok += 1
    minfull = np.array(minfull); minperp = np.array(minperp)
    print(f"  L_P - diag(R) PSD (global)             : {psd_full}/{ng}  "
          f"(lam_min: min={minfull.min():.3f} median={np.median(minfull):.3f})")
    print(f"  PSD on f-perp-1 (all g _|_ 1)          : {psd_perp}/{ng}  "
          f"(min eig on 1-perp: min={minperp.min():.3f})")
    print(f"  PSD on nodal V+ submatrix              : {psd_Vp}/{ng}")
    print(f"  PSD on nodal V- submatrix              : {psd_Vm}/{ng}")
    print(f"  PSD on (R>=0) submatrix (drop neg-R hubs): {psd_nohub}/{ng}")
    print(f"  f^T(L_P-diag R)f = -Q >= 0 (the conjecture): {fQf_ok}/{ng}")

    # ---------------- TASK 3 ----------------
    print("\n" + "=" * 76)
    print("TASK 3 — incidence factorisation: Open = ||B_open f||^2 (SOS)")
    print("=" * 76)
    r_sos = mx(lambda q: q['Open'] - sum(
        q['P'][a, b] * (q['f'][a] - q['f'][b]) ** 2
        for a in range(q['n']) for b in range(a + 1, q['n'])))
    print(f"  Open == sum_{{a<b}} P_ab (f_a-f_b)^2  (= ||B_open f||^2): residual {r_sos:.2e}")
    print("  => L_P = B_open^T B_open with one row per open cherry (a,c,b): +1 at a, -1 at b.")
    print("     Open is a MANIFEST sum of squares. diag(R) is sign-indefinite (R_v<0 on hubs),")
    print("     so 'Gram >= diagonal' fails exactly where R_v>0 exceeds the open-cherry support.")
    # quantify: how much open-cherry support sits on high-R vs the demand
    covered = 0
    for q in data:
        # per-vertex open-degree p_v vs R_v^+ : is open support where demand is?
        Rp = np.maximum(q['Rvec'], 0)
        if (q['pdeg'] >= Rp - 1e-9).all():
            covered += 1
    print(f"  per-vertex open-degree p_v >= R_v^+ : {covered}/{ng} (diagonal-domination fails)")

    # ---------------- TASK 4 ----------------
    print("\n" + "=" * 76)
    print("TASK 4 — A^2 recursion on non-edges")
    print("=" * 76)
    r_rec = mx(lambda q: float(np.max(np.abs(
        q['A2'] @ q['f'] - (q['A'] @ (q['D'] @ q['f']) - q['lam'] * (q['D'] @ q['f'] - q['lam'] * q['f']))))))
    print(f"  A^2 f == A D f - lam(D f - lam f)            : residual {r_rec:.2e}")
    # (P f)_v = (A D f)_v - lam(d_v-lam)f_v - d_v f_v - (M f)_v
    r_Pf = mx(lambda q: float(np.max(np.abs(
        q['P'] @ q['f'] - ((q['A'] @ (q['D'] @ q['f'])) - q['lam'] * (q['d'] - q['lam']) * q['f']
                           - q['d'] * q['f'] - q['M'] @ q['f'])))))
    print(f"  (P f)_v == (ADf)_v - lam(d_v-lam)f_v - d_v f_v - (Mf)_v : residual {r_Pf:.2e}")
    # quadratic form: f^T P f = f^T(ADf) - lam f^T(D-lam)f - fDf - f^T M f
    # and Open = p.f^2 - f^T P f.  Project the recursion onto the open quadratic form.
    r_fPf = mx(lambda q: float(q['f'] @ q['P'] @ q['f'])
               - (float(q['f'] @ q['A'] @ (q['D'] @ q['f'])) - q['lam'] * (q['fDf'] - q['lam'])
                  - q['fDf'] - float(q['f'] @ q['M'] @ q['f'])))
    print(f"  f^T P f == f^TADf - lam(fDf-lam) - fDf - f^TMf : residual {r_fPf:.2e}")
    print("  => the A^2 recursion fixes f^T P f exactly, but Open = p.f^2 - f^T P f mixes the")
    print("     open-DEGREE diagonal p.f^2 with the recursion; no non-edge projection isolates")
    print("     Open >= diag(R) (it reproduces -Q, circular).")

    print("\n" + "=" * 76)
    print("SUMMARY")
    print("=" * 76)
    print(f"  Open >= lam2(L_P)||f_perp||^2 spectral bound holds {lbound_ok}/{ng}, but")
    print(f"  lam2(L_P) >= sum R f^2 closes only {okA}/{ng}: spectral floor too weak.")
    print(f"  L_P - diag(R) PSD: global {psd_full}/{ng}, 1-perp {psd_perp}/{ng}, "
          f"drop-hubs {psd_nohub}/{ng}: no fixed-operator certificate.")
    print("  Open = ||B_open f||^2 exact SOS; recursion fixes f^TPf but only reproduces -Q.")


if __name__ == "__main__":
    main()
