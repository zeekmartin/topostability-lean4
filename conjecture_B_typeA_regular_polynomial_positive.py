"""
TYPE A regular-core gap = lam(rho-lam+1) + K/D : secular polynomial + positivity proof.

K = (3lam-lam*rho-2) + (2lam+rho-2)(2-lam)^2/2 + (3-rho)(2-lam) - lam(4-rho-lam)^2/m
D = 1 + (2-lam)^2/2 + (3-lam)^2/(n-3),   m = rho(n-1)/2 + 2.

TASK1 secular P(lam,rho,n)=0 (mean-field 3x3 reduction).
TASK2 gap = Num/Den (sympy).
TASK3 reduce Num mod P; TASK4 interval positivity; TASK5 rho=n-2, fixed, qn.
Run: python conjecture_B_typeA_regular_polynomial_positive.py
"""
import numpy as np
import networkx as nx
import sympy as sp


# ---------- PART A: numerical check of secular candidates ----------
def actual_lambda(rho, n, seed=2, complete=False):
    nH = n - 1
    H = nx.complete_graph(nH) if complete else nx.random_regular_graph(rho, nH, seed=seed)
    H = nx.convert_node_labels_to_integers(H)
    a = 0; nbrs = set(H.neighbors(a))
    b = next((u for u in range(1, nH) if u not in nbrs and u != a), 1)
    G = nx.Graph(H); G.add_node(nH); G.add_edge(nH, a); G.add_edge(nH, b)
    L = nx.laplacian_matrix(G, nodelist=list(G.nodes())).toarray().astype(float)
    return float(np.linalg.eigvalsh(L)[1])


def meanfield_lambda(rho, n):
    # cubic P(lam)= (2-lam)[lam^2-lam(rho+1+beta)+beta] - 2(beta-lam),  beta=2rho/(n-3)
    beta = 2 * rho / (n - 3)
    lam = sp.symbols('lam', real=True)
    P = (2 - lam) * (lam ** 2 - lam * (rho + 1 + beta) + beta) - 2 * (beta - lam)
    roots = [complex(r).real for r in sp.nroots(sp.Poly(P, lam)) if abs(complex(r).imag) < 1e-9]
    roots = [r for r in roots if 0.5 < r < 2.0 + 1e-9]   # the bottleneck root near 2
    return max(roots) if roots else float('nan')


def partA():
    print("=" * 84)
    print("PART A — secular accuracy: actual lam2 vs mean-field cubic vs (2-lam)(rho-lam+1)=2")
    print("=" * 84)
    print(f"  {'rho':>4} {'n':>5} {'lam_actual':>11} {'lam_meanfield':>14} {'lam_approx':>11}")
    for n in [50, 100, 200]:
        for rho in [5, 10, 20, 50, n - 2]:
            if rho < 3 or rho > n - 2: continue
            comp = (rho == n - 2)
            if not comp and (rho * (n - 1)) % 2: continue   # n*d parity
            la = actual_lambda(rho, n, complete=comp)
            lm = meanfield_lambda(rho, n)
            # approx: (2-lam)(rho-lam+1)=2 -> solve
            lam = sp.symbols('lam')
            ap = [complex(r).real for r in sp.nroots(sp.Poly((2 - lam) * (rho - lam + 1) - 2, lam))
                  if abs(complex(r).imag) < 1e-9 and 0.5 < complex(r).real < 2.01]
            print(f"  {rho:4d} {n:5d} {la:11.5f} {lm:14.5f} {(max(ap) if ap else float('nan')):11.5f}")


# ---------- PART B: symbolic gap ----------
def partB():
    lam, rho, n = sp.symbols('lambda rho n', positive=True)
    m = rho * (n - 1) / 2 + 2
    K = ((3 * lam - lam * rho - 2) + (2 * lam + rho - 2) * (2 - lam) ** 2 / 2
         + (3 - rho) * (2 - lam) - lam * (4 - rho - lam) ** 2 / m)
    D = 1 + (2 - lam) ** 2 / 2 + (3 - lam) ** 2 / (n - 3)
    gap = lam * (rho - lam + 1) + K / D
    Num, Den = sp.fraction(sp.together(gap))
    Num = sp.expand(Num); Den = sp.expand(Den)

    print("\n" + "=" * 84)
    print("TASK 2 — gap = Num/Den")
    print("=" * 84)
    print("  Den =", sp.factor(Den))
    print("  Num is a polynomial in (lambda, rho, n); degree in lambda:",
          sp.degree(sp.Poly(Num, lam)))

    print("\n" + "=" * 84)
    print("TASK 5a — complete core rho = n-2, lambda = 2  =>  10(n-3)/m ?")
    print("=" * 84)
    gap_cc = sp.simplify(gap.subs({rho: n - 2, lam: 2}))
    target = sp.simplify(sp.Rational(10) * (n - 3) / ((n - 2) * (n - 1) / 2 + 2))
    print("  gap(rho=n-2, lam=2) =", sp.simplify(gap_cc))
    print("  10(n-3)/m           =", target)
    print("  EQUAL:", sp.simplify(gap_cc - target) == 0)

    print("\n" + "=" * 84)
    print("TASK 3/4 — positivity of Num.  Substitute s = 2 - lambda (0 < s), study sign.")
    print("=" * 84)
    s = sp.symbols('s', positive=True)   # s = 2 - lambda in (0, ~0.73]
    Num_s = sp.expand(Num.subs(lam, 2 - s))
    Den_s = sp.expand(Den.subs(lam, 2 - s))
    print("  Den(s) sign (need >0):", sp.factor(Den_s))
    # Num_s as polynomial in s with coeffs in rho,n
    Ps = sp.Poly(Num_s, s)
    print("  Num(s) degree in s:", Ps.degree())
    # check coefficients' signs for the regime rho>=3, n>rho+1
    print("  Num(s) coefficients (low->high power of s), factored:")
    for k, c in enumerate(reversed(Ps.all_coeffs())):
        print(f"    s^{k}: {sp.factor(c)}")
    return Num, Den, lam, rho, n, s, Num_s, Den_s


def partB2(Num_s, Den_s, s, rho, n):
    print("\n" + "=" * 84)
    print("TASK 4 — positivity AT the secular root (whole-interval positivity already FAILS)")
    print("=" * 84)
    fNum = sp.lambdify((s, rho, n), Num_s, 'numpy')
    fDen = sp.lambdify((s, rho, n), Den_s, 'numpy')
    # (i) whole-interval: confirm Num changes sign
    bad = tested = 0
    for nn in [50, 100, 200]:
        for rr in [10, 20, 50]:
            if rr > nn - 2: continue
            for sv in np.linspace(1e-4, 2.0 / (rr - 1), 40):
                tested += 1
                if fNum(sv, rr, nn) <= 0 or fDen(sv, rr, nn) <= 0: bad += 1
    print(f"  (i) whole interval s in (0,2/(rho-1)]: Num<=0 at {bad}/{tested} points "
          f"=> NOT positive on whole interval (need the secular).")
    # (ii) AT the mean-field secular root
    print("  (ii) gap_model AT the mean-field secular root:")
    print(f"      {'rho':>4} {'n':>5} {'s*=2-lam':>9} {'Num(s*)':>12} {'Den(s*)':>12} {'gap_model':>10} {'>0':>4}")
    allpos = True
    for nn in [50, 100, 200, 500]:
        for rr in [5, 10, 20, 50, 100]:
            if rr > nn - 2: continue
            lam_mf = meanfield_lambda(rr, nn)
            if lam_mf != lam_mf: continue
            sv = 2 - lam_mf
            Nv = float(fNum(sv, rr, nn)); Dv = float(fDen(sv, rr, nn))
            g = Nv / Dv; allpos &= g > 0
            print(f"      {rr:4d} {nn:5d} {sv:9.5f} {Nv:12.3e} {Dv:12.3e} {g:10.5f} {str(g>0):>4}")
    print(f"  => gap_model > 0 at the secular root: {allpos}")


def partB3():
    print("\n" + "=" * 84)
    print("TASK 5b/5c — gap_model at the secular root for rho fixed and rho = q*n  (n grid)")
    print("=" * 84)
    print("  (substituting lam=2 is WRONG: gap is O(1/n) but hypersensitive to lam-2 ~ O(1/n);")
    print("   must evaluate at the secular root.)")
    lam, rho, n = sp.symbols('lambda rho n', positive=True)
    m = rho * (n - 1) / 2 + 2
    K = ((3 * lam - lam * rho - 2) + (2 * lam + rho - 2) * (2 - lam) ** 2 / 2
         + (3 - rho) * (2 - lam) - lam * (4 - rho - lam) ** 2 / m)
    D = 1 + (2 - lam) ** 2 / 2 + (3 - lam) ** 2 / (n - 3)
    gap = lam * (rho - lam + 1) + K / D
    fgap = sp.lambdify((lam, rho, n), gap, 'numpy')
    print(f"  {'regime':14s} {'n':>5} {'rho':>5} {'lam*':>8} {'gap_model':>11} {'gap*m/n=c':>10}")
    for nn in [50, 100, 200, 500, 1000]:
        for label, rr in [("fixed rho=10", 10), ("rho=n/2", nn // 2), ("rho=n-2", nn - 2)]:
            if rr > nn - 2 or rr < 3: continue
            lam_mf = meanfield_lambda(rr, nn)
            if lam_mf != lam_mf:                  # complete core: lam=2 exact
                lam_mf = 2.0
            g = float(fgap(lam_mf, rr, nn))
            mm = rr * (nn - 1) / 2 + 2
            print(f"  {label:14s} {nn:5d} {rr:5d} {lam_mf:8.5f} {g:11.6f} {g*mm/nn:10.4f}")


if __name__ == "__main__":
    partA()
    Num, Den, lam, rho, n, s, Num_s, Den_s = partB()
    partB2(Num_s, Den_s, s, rho, n)
    partB3()
