# Conjecture B — TYPE A: driver vs correction (the proposed proof refuted)

Proposed proof: `gap = λρ‖f_H‖² + correction` with the driver `λρ‖f_H‖² > 0` dominating a small
correction `|correction| ≤ C·η²`, `η² ≤ ‖source‖²/(γ−λ)²` (`poincare_on_block`). We test it exactly
on regular cores. **Verdict: the strategy fails — the correction is `O(1)`, not `O(η²)`.** Code:
[`conjecture_B_typeA_driver_vs_correction.py`](../conjecture_B_typeA_driver_vs_correction.py).

## TASK 1 — `‖f_H‖²` and the driver magnitude

`‖f_H‖² = 1 − x²`. The proposed lower bound uses the `(2−λ)²/2` piece, but for **genuine TYPE A**
(large `ρ`, `v₀` the bottleneck) `(2−λ)² ≈ ε₁² ≈ 4/ρ²` is negligible; the bulk/mean piece
`(3−λ)²/(n−3)` dominates. So `driver = λρ‖f_H‖² ≈ λρ(3−λ)²/n = O(1)` — e.g. `≈ 2.0` for the complete
core, **not** the hoped `λρ/n` (small). The driver is `O(1)`, the *same order as the gap is small*.

## TASK 2 — the correction is `O(1)`, not `O(η²)`

`correction = gap − driver`. `poincare_on_block` is valid (`η² ≤ ‖source‖²/(γ−λ)²`, verified), but
**`η²` is not what controls the correction**:

| ρ | n | λ | TYPE A | gap | driver | corr | η² | `|corr|/η²` | driver/`|corr|` |
|---|---|---|---|---|---|---|---|---|---|
| 6 | 100 | 1.45 | ✓ | 3.103 | 2.565 | +0.538 | 2.9e‑1 | 1.9 | 4.77 |
| 20 | 100 | 1.91 | ✓ | 0.560 | 0.619 | −0.059 | 6.2e‑3 | 9.4 | 10.56 |
| 50 | 100 | 1.98 | ✓ | 0.297 | 1.070 | −0.773 | 8.2e‑4 | 947 | 1.38 |
| 98 | 100 | 2.00 | ✓ | 0.200 | 2.000 | −1.800 | 2.1e‑4 | 8732 | 1.11 |
| 198 | 200 | 2.00 | ✓ | 0.100 | 2.000 | −1.900 | 5.1e‑5 | 37432 | 1.05 |

> **`|correction|/η² ∈ [0.3, 37432]` — it blows up.** As `ρ` grows the resolvent `η² → 0` (the block
> *is* flat), yet `|correction|` stays `O(1)`. The correction is dominated by the **`−λS²/m`** term
> (`0.11, 0.43, 1.24, 3.52, …`, `O(1)`, growing with `ρ`) and the degree-gradient terms — all
> **η-independent**. `poincare_on_block` bounds `η²` correctly, but `η²` is the *wrong* quantity.

## TASK 3 — does the driver dominate? (yes numerically, but circularly)

`driver > |correction|` holds `18/18` — but this is **not an independent proof**:

1. For genuine dense TYPE A (`corr < 0`, 8/16 rows), `driver > |corr| ⟺ driver − |corr| > 0 ⟺
   gap > 0`. It is literally a restatement of the conclusion.
2. The margin is **thin and vanishing**: `driver ≈ |correction|` (both `O(1)`, nearly cancelling),
   `gap = driver − |correction|` is the small `O(1/n)` residual. For the complete core
   `driver = 2.0`, `|corr| = 1.9`, ratio `→ 1` as `n` grows (`1.25 → 1.11 → 1.05`) — the "margin" *is*
   the gap. There is no `ρ³/n → ∞` separation.

So the proposed `driver ≫ |correction|` does not hold: `driver` and `|correction|` are the **same
`O(1)` order and nearly cancel**, exactly the `R″_∞ = −C_∞` leading cancellation seen throughout.

## TASK 4 — verification

All `gap > 0` (18/18). `|correction|/η²` unbounded (`→ 37432`), confirming `correction ≠ O(η²)`.
Small-`ρ` rows (`ρ = 4`) have `λ > γ` — **not TYPE A** (the core's own bottleneck dominates,
`f_v₀² ≈ 0.02`); there `corr > 0` and `gap > driver > 0` trivially, but they are outside the regime.
Within genuine TYPE A (`λ < γ`, 16 rows): `corr < 0` in 8, `driver/|corr| ∈ [1.05, 10.56]`.

## Conclusion — the strategy fails, and why

- **`correction` is `O(1)`, not `O(η²)`.** It is dominated by the deterministic `−λS²/m` and
  degree-gradient terms (η-independent), which `poincare_on_block` does **not** bound. The resolvent
  flatness `η² → 0` is real but irrelevant to the correction's size.
- **`driver ≈ |correction|` (both `O(1)`, nearly cancelling); `gap` is their `O(1/n)` residual.** So
  `driver > |correction|` is logically equivalent to `gap > 0` (for the dense regime) with a vanishing
  margin — no independent proof.
- **What actually proves `gap > 0`:** the exact `O(1)` balance, captured by
  `gap = λ(ρ−λ+1) + K/D` (`conjecture_B_typeA_regular_core_proof.md`). The **complete core** is the
  clean closed form (`gap = 10(n−3)/m`, manifestly positive); the general regular case needs the full
  `K/D` balance, not a driver-dominance bound.

The takeaway: a `poincare_on_block`-style `η`-bound cannot close TYPE A, because the obstruction lives
in the deterministic `S²/m` / degree terms, not the resolvent — the same conclusion as the Schur 2×2
analysis (`gap` is one order below the resolvent-controlled quantities).

## Lean
No new lemma (numerical refutation of a proof strategy). The valid closed-form handle remains the
complete-core `gap = 10(n−3)/m` and the exact reduction `gap = λ(ρ−λ+1) + x²K`.
