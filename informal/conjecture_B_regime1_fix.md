# Conjecture B — the one failing Regime-1 graph for the S-procedure

S-procedure: `M + α(L−λ₂I) ⪰ 0` on `1⊥` ⟹ `gap = λ₂G − B2′ ≥ 0` (`M = λ₂(D+A) − (λ₂/m)ddᵀ −
L_min`). `α = Δ+λ₂−1` certifies **276/277** Regime-1 (`Required ≤ 0`) graphs. Code:
[`conjecture_B_regime1_fix.py`](../conjecture_B_regime1_fix.py).

## TASK 1 — the failing graph

> **n = 37, m = 274, λ₂ = 1.880, Required = −0.0635 (≈ 0⁻), Δ = 20**, degree sequence
> `[2, 12, 12, …, 19, 20]` — a **degree-2 vertex amid a dense core**. `T/RHS = 0.170`.

It needs `α* = 21.909 = 1.0493·(Δ+λ₂−1)` (just **5% above** `α = Δ+λ₂−1 = 20.880`). This is a
**deg2+dense graph sitting just inside the Regime-1 boundary** (`Required = −0.064`, barely `≤ 0`):
the universal hard family (deg2+dense) is split by the regime boundary, and its Regime-1
representative is exactly the one graph where the regular formula `Δ+λ₂−1` is insufficient. Over all
277, `α*/(Δ+λ₂−1)` ranges `[0.32, 1.0493]` — only this one exceeds 1.

## TASK 2 — formulas certifying ALL 277 (numerically)

| α | certified | `max α*/α` |
|---|---|---|
| `Δ+λ₂−1` | 276/277 | 1.049 |
| `Δ+λ₂` | 276/277 | 1.001 |
| **`Δ+λ₂+1`** | **277/277** | 0.963 |
| **`Δ+2λ₂−1`** | **277/277** | 0.987 |
| **`1.05(Δ+λ₂−1)`** | **277/277** | 0.999 |
| **`2Δ`** | **277/277** | 0.548 |
| **`Δ+2λ₂`** | **277/277** | 0.975 |

Several simple formulas work. The cleanest generalisation of the regular `α = d+λ₂−1` is
**`α = Δ+2λ₂−1`** (the extra `+λ₂` absorbs the irregularity slack); `2Δ` is the safest (margin 2×).

## TASK 3 — these formulas do NOT close Regime 1 in Lean

**A numerical PSD certificate is not a proof.** Formalising "`M + α(L−λ₂I) ⪰ 0` on `1⊥` for all
Regime-1 graphs" requires *proving* a matrix is positive-semidefinite for every such graph — and
unlike the regular case, **there is no closed-form structure to exploit**:

- **Regular case (collapses):** `L_min = (d−1)L` *commutes* with `L`, so in `L`'s eigenbasis
  `M_α = gap·I` (a scalar matrix) — manifestly PSD. (`[L_min, L] = 0`, verified e.g. Petersen.)
- **Irregular failing graph (no collapse):** `L_min` does **not** commute with `L` —
  `‖[L_min, L]‖ = 557 ≠ 0`. There is no common eigenbasis; `M_α ⪰ 0` is a genuine, structureless
  matrix inequality of **conjecture strength** (it is exactly `B2′ ≤ λ₂G` plus PSD on the orthogonal
  bulk). Choosing `α = Δ+2λ₂−1` makes it *numerically* true but gives no algebraic proof.

So finding the α-formula **does not close Regime 1** — it only sharpens the regime-1 target. The
S-procedure is a valid *reduction* (PSD-on-`1⊥` ⟹ `gap ≥ 0`, the easy direction), but the PSD
hypothesis remains an unproven matrix inequality with no clean certificate for irregular graphs.

**The clean formalisable Regime-1 target stays `aggregate_triangle_poincare`** (`T ≤ λ₂fᵀDf`, holds
277/277 in Regime 1, and 580/580 overall), whose **regular case is already proved**
(`aggregate_triangle_poincare_regular`). The failing graph shows precisely why the irregular case is
hard: it is the deg2+dense bottleneck, where `L_min` (large on the dense core) does not align with
`L`'s eigenbasis.

## Conclusion

- **Failing graph identified:** the deg2+dense representative at the Regime-1 boundary
  (`n=37, Required ≈ 0⁻`, deg-2 vertex), needing `α* = 1.0493(Δ+λ₂−1)`.
- **Numerical fix:** `α = Δ+2λ₂−1` (or `Δ+λ₂+1`, `2Δ`) certifies all 277.
- **But Regime 1 is NOT closed:** the certificate `M_α ⪰ 0` has no closed form for irregular graphs
  (`[L_min, L] ≠ 0`); it is conjecture-strength, not algebra. No new Lean lemma is warranted (a
  sorry-requiring matrix-PSD statement would be false progress). The honest Lean target remains
  `aggregate_triangle_poincare` (regular case done; irregular = the deg2+dense obstruction).

## Lean
No new lemma this round. The S-procedure formula is a numerical certificate, not a proof; the regular
collapse `M_α = gap·I` (which *is* provable, via `[L_min,L]=0`) is already captured by
`aggregate_triangle_poincare_regular`. The irregular case has no analogous structure.
