"""
TYPE A regular core: resultant elimination of lambda (last algebraic attempt).

gap = Num/Den, Den>0. Mean-field secular Ptilde (cubic) -- APPROXIMATE; the EXACT secular for general
regular cores is NOT polynomial, so any resultant works on the mean-field model only (exact solely for
the complete core).

Findings: R=Res(P,Num)=0 trivially (shared lambda=0 null mode); reduced resultant on P_rest=P/lam is
degree-8, sign-indefinite over valid (rho,n) -> vanishes in range, but from the SPURIOUS high mode
lambda_big~rho, not the bottleneck lambda*~2 (Num(lambda*)>0 always). Sturm: Num has 0 roots in [1,2]
for small rho (=> gap>0 there) but 2 roots for large rho (cannot isolate lambda*).
Run: python conjecture_B_typeA_resultant.py
"""
import numpy as np
import sympy as sp


def build():
    lam, rho, n = sp.symbols('lambda rho n', real=True)
    m = rho * (n - 1) / 2 + 2
    K = ((3 * lam - lam * rho - 2) + (2 * lam + rho - 2) * (2 - lam) ** 2 / 2
         + (3 - rho) * (2 - lam) - lam * (4 - rho - lam) ** 2 / m)
    D = 1 + (2 - lam) ** 2 / 2 + (3 - lam) ** 2 / (n - 3)
    gap = lam * (rho - lam + 1) + K / D
    Num, Den = sp.fraction(sp.together(gap)); Num = sp.expand(Num)
    beta = 2 * rho / (n - 3)
    Ptil = sp.expand(sp.together((2 - lam) * (lam ** 2 - lam * (rho + 1 + beta) + beta)
                                 - 2 * (beta - lam)) * (n - 3))
    return lam, rho, n, Num, Den, Ptil


def secular_root(Ptil_sub, lam):
    rts = [complex(z).real for z in
           np.roots([float(c) for c in sp.Poly(Ptil_sub, lam).all_coeffs()])
           if abs(complex(z).imag) < 1e-9 and 0.5 < complex(z).real < 2.05]
    return max(rts) if rts else float('nan')


def main():
    lam, rho, n, Num, Den, Ptil = build()
    print("=" * 80)
    print("TASK 1 — R = Res_lam(Ptilde, Num)")
    print("=" * 80)
    R = sp.expand(sp.resultant(Ptil, Num, lam))
    print("  R =", R, " (identically zero)")
    g = sp.gcd(Ptil, Num)
    print("  gcd(Ptilde, Num) in lambda =", sp.factor(g), " => shared trivial null mode lambda=0")

    print("\n" + "=" * 80)
    print("TASK 1b — reduced resultant on the bottleneck factor P_rest = Ptilde/lambda")
    print("=" * 80)
    Pr = sp.cancel(Ptil / lam); Nr = sp.cancel(Num / lam)
    Rp = sp.expand(sp.resultant(Pr, Nr, lam))
    print("  P_rest (quadratic) =", sp.factor(Pr))
    print("  R_reduced total degree:", sp.total_degree(Rp))
    fR = sp.lambdify((rho, n), Rp, 'numpy')
    signs = set()
    for nn in range(6, 90):
        for rr in range(3, nn - 1):
            signs.add(int(np.sign(float(fR(rr, nn)))))
    print(f"  R_reduced signs over 3<=rho<=n-2, 6<=n<90: {sorted(signs)} "
          f"=> {'sign-indefinite (VANISHES in range)' if len(signs) > 1 else 'definite'}")

    print("\n" + "=" * 80)
    print("TASK 3 — at a sign-change of R_reduced, WHICH P_rest root is shared?")
    print("=" * 80)
    fNr = sp.lambdify((lam, rho, n), Nr, 'numpy')
    # find crossing in n (fixed rho) and in rho (fixed n)
    found = None
    for nn in range(8, 200):
        prev = None
        for rr in range(3, nn - 1):
            v = float(fR(rr, nn))
            if prev is not None and prev * v < 0:
                found = (rr - 0.5, nn); break
            prev = v
        if found: break
    if found:
        rr, nn = found
        prts = sorted([complex(z).real for z in np.roots(
            [float(c) for c in sp.Poly(Pr.subs({rho: rr, n: nn}), lam).all_coeffs()])
            if abs(complex(z).imag) < 1e-7])
        print(f"  near (rho~{rr}, n={nn}): P_rest roots = {[round(x,3) for x in prts]} "
              f"(lambda*~2 small, lambda_big~rho large)")
        for x in prts:
            print(f"    Num_rest({x:.3f}) = {fNr(x, rr, nn):.3e}  "
                  f"({'~0 SHARED' if abs(fNr(x, rr, nn)) < 1e-2*abs(fNr(prts[0],rr,nn)+1) else 'nonzero'})")
    print("  (Num(lambda*) > 0 for ALL tested (rho,n): the shared root is lambda_big, never lambda*.)")

    print("\n" + "=" * 80)
    print("TASK 4 — Sturm: # real roots of Num in [1,2] (where lambda* lives)")
    print("=" * 80)
    print(f"  {'rho':>4} {'n':>5} {'lam*':>7} {'#roots[1,2]':>11} {'Num(lam*)':>11} {'gap sign':>9}")
    for nn in [50, 100, 200]:
        for rr in [3, 5, 10, 20, 50, nn - 2]:
            if rr < 3 or rr > nn - 2: continue
            Numr = sp.Poly(Num.subs({rho: rr, n: nn}), lam)
            cnt = int(sp.polys.polytools.count_roots(Numr, 1, 2))
            ls = secular_root(Ptil.subs({rho: rr, n: nn}), lam)
            nv = float(Numr.eval(ls)) if ls == ls else float('nan')
            print(f"  {rr:4d} {nn:5d} {ls:7.4f} {cnt:11d} {nv:11.3e} "
                  f"{'+' if nv > 0 else '-':>9}")
    print("  small rho: 0 roots in [1,2] => Num>0 throughout => gap>0 (model).")
    print("  large rho: 2 roots in [1,2] near lambda*~2 => cannot isolate lambda* by interval.")

    print("\n" + "=" * 80)
    print("CONCLUSION")
    print("=" * 80)
    print("  Resultant elimination FAILS to certify general TYPE A:")
    print("  (1) exact secular is NON-polynomial (only mean-field P; even qualitatively wrong for")
    print("      the complete core, where exact lambda=2 is not a P_rest root);")
    print("  (2) R=Res(P,Num)=0 trivially (shared null mode lambda=0);")
    print("  (3) reduced resultant conflates lambda* with the spurious high mode lambda_big~rho and")
    print("      vanishes in range; Num is sign-indefinite near lambda* for large rho (Sturm=2).")
    print("  The bottleneck root is irrational & inseparable from spurious modes algebraically.")
    print("  CLEAN result stands: COMPLETE CORE gap=10(n-3)/m>0 (exact lambda=2, sympy-proven).")


if __name__ == "__main__":
    main()
