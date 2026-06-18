"""
Domain-local triangle-weighted Poincare on a single nodal domain.

On a sign domain D (V+ or V-), set x_v = |f_v| >= 0. Internal triangle weights W_ab = t_ab
(ab in E(D)).  tau^D_v = sum_{u in D, u~v} t_vu.  Full degree d_v, full triangle degree tau_v.

    T_D      = sum_{ab in E(D)} t_ab (x_a - x_b)^2           ( = x^T (diag(tau^D) - W_D) x )
    C_same_D = 2 sum_{ab in E(D)} t_ab x_a x_b
    Delta_D  = sum_{v in D} (tau_v - lam2 d_v) x_v^2          (full tau_v, full d_v)

TARGET (domain-local):   T_D <= lam2 * sum_{v in D} d_v x_v^2     <=>   C_same_D >= Delta_D'
  where Delta_D' uses tau^D_v (domain-restricted).  Delta_D (full tau) >= Delta_D'.

TASK 1: Rayleigh quotient of the triangle-weighted Laplacian L^t_D vs D_D.
TASK 2: lam_D = T_D / sum_D d_v x_v^2 ;  compare to lam2(G).  generalized mu_max(L^t_D, D_D).
TASK 3: is x=|f| a Perron / sub- / super-solution of the weighted adjacency W_D?
TASK 4: row equation  A_D x = (D - lam2) x + b,  b>=0   (unweighted, exact).
        A^2 f = A D f - lam2 (D - lam2) f  (exact triangle-level identity).
TASK 5: POINTWISE Collatz-Wielandt test  L^t_D x <= lam2 D_D x, i.e.
            sum_{u in D,u~v} t_vu (x_v - x_u) <= lam2 d_v x_v   for every v in D.
        If true, x>=0 gives the quadratic form for free.

Run: python conjecture_B_domain_triangle_perron.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques


def domain_data(G):
    """Return per-domain dicts of all task quantities for both nodal domains."""
    nodes = list(G.nodes())
    L = nx.laplacian_matrix(G, nodelist=nodes).toarray().astype(float)
    d = L.diagonal(); A = np.diag(d) - L
    ev, V = np.linalg.eigh(L); lam = ev[1]
    f = V[:, 1] / np.linalg.norm(V[:, 1])
    A2 = A @ A
    M = A * A2                       # M_vu = t_vu on edges

    # exact A^2 identity (global):  A^2 f = A D f - lam (D - lam) f
    lhs = A2 @ f
    rhs = A @ (d * f) - lam * (d * f - lam * f)
    a2_res = float(np.max(np.abs(lhs - rhs)))

    out = []
    for sign in (+1, -1):
        Dm = (f * sign) >= 0 if sign == +1 else (f * 1) < 0
        # domain mask: V+ = f>=0 ; V- = f<0
        Dm = (f >= 0) if sign == +1 else (f < 0)
        idx = np.where(Dm)[0]
        if len(idx) < 2:
            continue
        x = np.abs(f[idx])
        AD = A[np.ix_(idx, idx)]            # internal adjacency
        WD = M[np.ix_(idx, idx)]            # internal triangle weights
        dD = d[idx]                          # full degrees
        tauD = WD.sum(1)                     # domain-restricted triangle degree
        LtD = np.diag(tauD) - WD             # triangle-weighted Laplacian on D
        DD = np.diag(dD)

        T_D = float(x @ LtD @ x)
        denom = float((dD * x * x).sum())
        lam_D = T_D / denom if denom > 1e-15 else float('nan')

        # generalized eigenproblem  L^t_D y = mu D_D y
        try:
            gv = np.linalg.eigvalsh(np.linalg.inv(DD) @ LtD)  # D_D spd
            mu_max = float(gv.max())
        except Exception:
            mu_max = float('nan')

        # Perron test on W_D:  is x an eigenvector / sub / super solution?
        Wx = WD @ x
        ratio = Wx / np.maximum(x, 1e-15)    # (W_D x)_v / x_v
        rho_WD = float(np.linalg.eigvalsh(WD).max()) if len(idx) else 0.0

        # row equation (unweighted):  A_D x = (d - lam) x + b
        b = np.array([sum(abs(f[u]) for u in range(len(f))
                          if A[idx[k], u] > 0 and not Dm[u]) for k in range(len(idx))])
        row_res = float(np.max(np.abs(AD @ x - ((dD - lam) * x + b))))

        # TASK 5 pointwise:  sum_{u in D} t_vu (x_v - x_u) <= lam d_v x_v
        pw_lhs = tauD * x - WD @ x           # (L^t_D x)_v
        pw_rhs = lam * dD * x                 # (lam D_D x)_v
        pw_viol = pw_lhs - pw_rhs            # want <= 0
        pw_ok = bool(np.all(pw_viol <= 1e-9))
        pw_worst = float(pw_viol.max())
        # normalized worst (relative to lam d_v x_v scale)
        pw_worst_rel = float((pw_viol / np.maximum(np.abs(pw_rhs), 1e-12)).max())

        out.append(dict(sign=sign, nD=len(idx), lam=lam, T_D=T_D, denom=denom,
                        lam_D=lam_D, mu_max=mu_max, rho_WD=rho_WD,
                        ratio_min=float(ratio.min()), ratio_max=float(ratio.max()),
                        ratio_std=float(ratio.std()), row_res=row_res,
                        pw_ok=pw_ok, pw_worst=pw_worst, pw_worst_rel=pw_worst_rel,
                        a2_res=a2_res))
    return out


def families():
    fam = []
    for fam_, G in corpus():
        fam.append((fam_, G))
    extra = []
    for m in (5, 10, 20, 40, 80):
        for Lb in (0, 1, 3):
            extra.append(("barbell", nx.barbell_graph(m, Lb)))
    for a, b in ((5, 5), (20, 20), (40, 40), (5, 40), (3, 60)):
        extra.append(("glue", glue(a, b)))
    for m, k in ((10, 2), (20, 2), (40, 2), (15, 4)):
        extra.append(("chain", chain_cliques(m, k)))
    return fam + extra


def main():
    rows = []
    a2_max = 0.0
    for fam, G in families():
        if G.number_of_nodes() < 4 or not nx.is_connected(G):
            continue
        try:
            ds = domain_data(G)
        except Exception:
            continue
        for r in ds:
            if not np.isfinite(r['lam']) or r['lam'] < 1e-9 or r['denom'] < 1e-12:
                continue
            r['fam'] = fam
            rows.append(r)
            a2_max = max(a2_max, r['a2_res'])

    n = len(rows)
    print("=" * 90)
    print(f"nodal domains analysed: {n}")
    print(f"\n[exact identity]  A^2 f = A D f - lam (D - lam) f :  max residual = {a2_max:.2e}")
    print(f"[exact identity]  row eq  A_D x = (d-lam)x + b      :  max residual = "
          f"{max(r['row_res'] for r in rows):.2e}")

    print("\n--- TASK 1/2: domain Rayleigh lam_D = T_D / (sum d_v x_v^2)  vs  lam2(G) ---")
    rd = np.array([r['lam_D'] / r['lam'] for r in rows])
    print(f"  lam_D / lam2 :  min={rd.min():.4f}  median={np.median(rd):.4f}  max={rd.max():.4f}")
    print(f"  T_D <= lam2 * sum d_v x_v^2  holds: {int((rd <= 1 + 1e-9).sum())}/{n}")
    mm = np.array([r['mu_max'] / r['lam'] for r in rows if np.isfinite(r['mu_max'])])
    print(f"  generalized mu_max(L^t_D,D_D)/lam2 : min={mm.min():.3f} median={np.median(mm):.3f} "
          f"max={mm.max():.3f}")
    print(f"  -> mu_max > lam2 (x is SPECIAL, not worst-case) in "
          f"{int((mm > 1 + 1e-9).sum())}/{len(mm)} domains")

    print("\n--- TASK 3: is x=|f| a Perron / sub-solution of W_D (triangle adjacency)? ---")
    rstd = np.array([r['ratio_std'] for r in rows])
    print(f"  (W_D x)/x  coeff spread (std):  median={np.median(rstd):.3f} "
          f"(0 would mean x is an eigenvector)")
    # subsolution: W_D x <= rho x ?  super: >= ?
    sub = sum(1 for r in rows if r['ratio_max'] <= r['rho_WD'] + 1e-9)
    sup = sum(1 for r in rows if r['ratio_min'] >= r['rho_WD'] - 1e-9)
    print(f"  W_D x <= rho(W_D) x  (subsolution everywhere): {sub}/{n}")
    print(f"  W_D x >= rho(W_D) x  (supersolution)         : {sup}/{n}")

    print("\n--- TASK 5: POINTWISE Collatz-Wielandt  L^t_D x <= lam2 D_D x ? ---")
    pw = sum(1 for r in rows if r['pw_ok'])
    worst = np.array([r['pw_worst_rel'] for r in rows])
    print(f"  pointwise inequality holds (all v in domain): {pw}/{n}")
    print(f"  worst relative violation (max over v of (L^t x - lam D x)/(lam d x)):")
    print(f"     min={worst.min():.4f}  median={np.median(worst):.4f}  max={worst.max():.4f}")
    if pw < n:
        bad = [r for r in rows if not r['pw_ok']]
        print(f"  FAILS in {len(bad)} domains; sample:")
        for r in sorted(bad, key=lambda r: -r['pw_worst_rel'])[:6]:
            print(f"     fam={r['fam']:14s} nD={r['nD']:3d} lam2={r['lam']:.3f} "
                  f"worst_rel={r['pw_worst_rel']:+.3f}  lam_D/lam2={r['lam_D']/r['lam']:.3f}")
    print("=" * 90)


if __name__ == "__main__":
    main()
