"""
Fix the 1 failing Regime-1 graph for the S-procedure  M + alpha(L-lam2 I) >= 0 on 1-perp.
alpha=Delta+lam2-1 certifies 276/277 (Required<=0).  Find the failure; test nearby formulas.
Run: python conjecture_B_regime1_fix.py
"""
import numpy as np
import networkx as nx
from conjecture_B_three_regimes_chain import build, sproc_ok, alpha_star, all_graphs


def main():
    data = [build(G) for G in all_graphs()]
    r1 = [q for q in data if q['Required'] <= 1e-7]
    print(f"Regime 1 (Required<=0): {len(r1)} graphs\n")

    # ---- TASK 1: identify failures of alpha = Delta+lam2-1 ----
    print("=" * 72)
    print("TASK 1 — failures of alpha = Δ+lam2-1")
    print("=" * 72)
    fails = []
    for q in r1:
        a = q['dmax'] + q['lam'] - 1
        if not sproc_ok(q, a):
            fails.append(q)
    print(f"  failures: {len(fails)}/{len(r1)}")
    for q in fails:
        ast = alpha_star(q)
        degs = sorted(int(x) for x in q['d'])
        print(f"  n={q['n']} m={q['m']} lam2={q['lam']:.4f} Required={q['Required']:.4e} "
              f"Δ={q['dmax']:.0f} α(Δ+λ-1)={q['dmax']+q['lam']-1:.3f} α*={ast:.3f} "
              f"ratio α*/(Δ+λ-1)={ast/(q['dmax']+q['lam']-1):.4f}")
        print(f"     deg seq (sorted): min={degs[0]} max={degs[-1]} "
              f"[{degs[:5]}...{degs[-5:]}]  T/RHS={q['T']/q['RHS']:.4f}")

    # ---- TASK 2: try nearby formulas, require ALL 277 ----
    print("\n" + "=" * 72)
    print("TASK 2 — formulas that certify ALL Regime-1 graphs")
    print("=" * 72)
    forms = {
        "Δ+λ-1": lambda q: q['dmax'] + q['lam'] - 1,
        "Δ+λ": lambda q: q['dmax'] + q['lam'],
        "Δ+λ+1": lambda q: q['dmax'] + q['lam'] + 1,
        "Δ+2λ-1": lambda q: q['dmax'] + 2 * q['lam'] - 1,
        "1.05(Δ+λ-1)": lambda q: 1.05 * (q['dmax'] + q['lam'] - 1),
        "1.1(Δ+λ-1)": lambda q: 1.1 * (q['dmax'] + q['lam'] - 1),
        "2Δ": lambda q: 2 * q['dmax'],
        "Δ+λ-1+λ²/Δ?": lambda q: q['dmax'] + q['lam'] - 1 + q['lam'] ** 2 / max(q['dmax'], 1),
        "Δ": lambda q: q['dmax'],
        "Δ+2λ": lambda q: q['dmax'] + 2 * q['lam'],
    }
    for name, af in forms.items():
        ok = sum(1 for q in r1 if sproc_ok(q, af(q)))
        worstratio = max((alpha_star(q) / af(q)) for q in r1 if af(q) > 1e-9)
        tag = "  <-- ALL" if ok == len(r1) else ""
        print(f"  α = {name:16s}: {ok}/{len(r1)}  (max α*/α = {worstratio:.3f}){tag}")

    # margin of the failing graph under the best formula
    print("\n" + "=" * 72)
    print("note: α* is graph-dependent (max ratio to Δ+λ-1 is the issue). check structure of fail.")
    print("=" * 72)
    # is alpha* /(Delta+lam-1) bounded? report distribution over ALL r1
    ratios = np.array([alpha_star(q) / (q['dmax'] + q['lam'] - 1) for q in r1
                       if q['dmax'] + q['lam'] - 1 > 1e-9])
    print(f"  α*/(Δ+λ-1) over Regime 1: min={ratios.min():.3f} median={np.median(ratios):.3f} "
          f"max={ratios.max():.4f}  (>1 on {int((ratios>1.0001).sum())}/{len(ratios)})")


if __name__ == "__main__":
    main()
