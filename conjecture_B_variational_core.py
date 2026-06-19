"""
Variational attack on the final reduced target  C + R'' >= 0  (= lam2 G - B2').

f = Fiedler (Lf=lam2 f, f _|_ 1, ||f||=1). Minimality: for any phi _|_ 1,
   Q(phi) := phi^T (L - lam2 I) phi >= 0.
Goal: write  gap := C + R'' = Q(phi) + (manifestly nonneg remainder)  for an explicit phi,
so that gap >= 0 follows.

R'' = lam2(fDf - lam2 + 1 - S^2/m),  C = sum_{edges,h higher-deg}(d_h-d_l)f_h(f_h-f_l).
C = N + A/2,  N=1/2 sum|d_a-d_b|g^2,  A=Cov_L(d,f^2);  C = f^T(1/2 diag(Ld) + 1/2 L_W) f,
  L_W = weighted Laplacian with edge weights W_ab=|d_a-d_b|.

TASK1 test perturbations phi (project to 1-perp), compute Q(phi), rem = gap - Q(phi).
TASK2/3 search exact gap = Q(phi) + nonneg.
TASK4 deg2+dense scaling sharpness.
Run: python conjecture_B_variational_core.py
"""
import numpy as np
import networkx as nx
from conjecture_B_nodal_decomposition import corpus
from conjecture_B_same_sign_reservoir import glue, chain_cliques
from conjecture_B_B2prime_scaling import deg2_dense


def setup(G):
    nodes = list(G.nodes()); idx = {u: i for i, u in enumerate(nodes)}; n = len(nodes)
    A = nx.to_numpy_array(G, nodelist=nodes); d = A.sum(1)
    L = np.diag(d) - A
    ev, U = np.linalg.eigh(L); lam = ev[1]; f = U[:, 1]; f = f / np.linalg.norm(f)
    m = G.number_of_edges(); S = float(d @ f); fDf = float(d @ (f * f))
    # gap = lam2 G - B2'
    es = [(idx[a], idx[b]) for a, b in G.edges()]
    B2 = 0.0; Gsum = 0.0
    Wmat = np.zeros((n, n))
    for a, b in es:
        g = f[a] - f[b]; h = f[a] + f[b]
        B2 += (min(d[a], d[b]) - 1) * g * g
        Gsum += h * h
        w = abs(d[a] - d[b]); Wmat[a, b] = w; Wmat[b, a] = w
    Gvar = Gsum - S ** 2 / m
    gap = lam * Gvar - B2
    L_W = np.diag(Wmat.sum(1)) - Wmat
    Ld = L @ d
    return dict(n=n, m=m, lam=lam, d=d, f=f, L=L, S=S, fDf=fDf, gap=gap, L_W=L_W, Ld=Ld)


def Qperp(q, phi):
    """phi^T(L-lam I)phi after projecting phi to 1-perp."""
    n = q['n']; phi = phi - phi.mean()
    return float(phi @ q['L'] @ phi) - q['lam'] * float(phi @ phi)


def candidates(q):
    d, f, lam = q['d'], q['f'], q['lam']
    dbar = d.mean()
    return {
        'Df': d * f,
        'sqrtD f': np.sqrt(d) * f,
        '(D-lam)f': (d - lam) * f,
        '(D-dbar)f': (d - dbar) * f,
        'L_W f': q['L_W'] @ f,
        'M_C f': 0.5 * (q['Ld'] * f) + 0.5 * (q['L_W'] @ f),
        'd': d.astype(float),
        'Ld.*f': q['Ld'] * f,
    }


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
    data = [setup(G) for G in graphs()]
    ng = len(data); tol = 1e-7
    names = list(candidates(data[0]).keys())

    print("=" * 80)
    print("TASK 1/3 — for each phi: rem = gap - Q(phi);  want rem >= 0 AND manifestly nonneg")
    print("=" * 80)
    print(f"  {'phi':12s} {'rem>=0':>8} {'min rem':>10} {'med rem':>10} {'corr(gap,Q)':>12} "
          f"{'med Q/gap':>10}")
    for name in names:
        rems = []; Qs = []; gaps = []
        for q in data:
            phi = candidates(q)[name]
            Q = Qperp(q, phi)
            rems.append(q['gap'] - Q); Qs.append(Q); gaps.append(q['gap'])
        rems = np.array(rems); Qs = np.array(Qs); gaps = np.array(gaps)
        nneg = int((rems >= -tol).sum())
        cc = np.corrcoef(gaps, Qs)[0, 1] if Qs.std() > 1e-12 else float('nan')
        rq = np.array([Qs[i] / gaps[i] for i in range(ng) if abs(gaps[i]) > 1e-9])
        print(f"  {name:12s} {nneg:4d}/{ng} {rems.min():10.4f} {np.median(rems):10.4f} "
              f"{cc:12.3f} {np.median(rq):10.3f}")
    print("  rem>=0 on ALL graphs => gap >= Q(phi) >= 0 is a valid lower bound via that phi.")

    # scaled single-phi: best alpha gives gap >= Q(alpha phi)=alpha^2 Q(phi); the *natural* test is
    # whether gap - Q(phi) is itself a recognizable nonneg form (variance/Dirichlet). Check rem vs
    # known nonneg quantities.
    print("\n" + "=" * 80)
    print("TASK 3 — is rem (for the best phi) a recognizable nonnegative form?")
    print("=" * 80)
    # pick phi with rem>=0 on all graphs and smallest median rem (tightest)
    best = None
    for name in names:
        rems = np.array([q['gap'] - Qperp(q, candidates(q)[name]) for q in data])
        if (rems >= -tol).all():
            if best is None or np.median(rems) < best[1]:
                best = (name, float(np.median(rems)))
    if best:
        print(f"  tightest all-nonneg phi: {best[0]} (median rem {best[1]:.4f})")
    else:
        print("  NO candidate phi has rem>=0 on all graphs (none gives a valid bound alone).")

    print("\n" + "=" * 80)
    print("TASK 4 — deg2+dense scaling: do gap and the best Q(phi) both ~ n^-0.9 ?")
    print("=" * 80)
    ns = [50, 100, 200, 500, 1000, 2000]
    rows = [setup(deg2_dense(n)) for n in ns]
    print(f"  {'n':>5} {'gap':>10}" + "".join(f"{nm[:9]:>11}" for nm in names))
    for n, q in zip(ns, rows):
        line = f"  {n:5d} {q['gap']:10.5f}"
        for nm in names:
            line += f"{Qperp(q, candidates(q)[nm]):11.4f}"
        print(line)
    def fit(ys, lab):
        ys = np.array(ys)
        if np.all(np.abs(ys) > 1e-14):
            a = np.polyfit(np.log(ns), np.log(np.abs(ys)), 1)
            print(f"    |{lab}| ~ n^{a[0]:.3f}")
    fit([q['gap'] for q in rows], "gap")
    for nm in names:
        fit([Qperp(q, candidates(q)[nm]) for q in rows], f"Q({nm})")

    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print("  Minimality gives Q(phi)>=0 for all phi _|_ 1. A proof needs gap = Q(phi) + nonneg")
    print("  with EXPLICIT phi. Report above which phi (if any) has gap>=Q(phi) on all graphs and")
    print("  whether the remainder is a recognizable nonneg form / scales like the deg2+dense margin.")


if __name__ == "__main__":
    main()
