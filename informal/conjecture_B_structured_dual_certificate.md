# Conjecture B — structured spectral multipliers for the dual certificate

Setup: `gap = fᵀMf ≥ 0`, `M = λ₂(D+A) − (λ₂/m)ddᵀ − L_min` (`L_min` = Laplacian, weights
`min(d_a,d_b)−1`), `M·1 = 0`, `(L−λ₂I)f = 0`. Certificate: find symmetric `Λ` with
`M' := M + Λ(L−λ₂I) + (L−λ₂I)Λ ⪰ 0` on `1⊥` (then `gap ≥ 0`, since the multiplier term vanishes on
`f`). Scalar `α` is exhausted (`α* ~ n²` on deg2+dense). Code:
[`conjecture_B_structured_dual_certificate.py`](../conjecture_B_structured_dual_certificate.py),
566 graphs.

## The key dichotomy: f-coupling vs u-block

In the Laplacian eigenbasis `{1, f, u₃,…,u_n}` (`Lu_k = λ_k`, `λ_k > λ₂`), the obstruction has two
parts:

1. the **f-coupling** `b_k = fᵀM u_k` (the off-diagonal `M`-row of the Fiedler), and
2. the **u-block** `M_uu` (`M` restricted to `span{u₃,…,u_n}`).

**Any `Λ` that commutes with `L`** (scalar `αI`, polynomial `aI+bL+cL²`, pseudoinverse `(L−λ₂I)⁺`)
**annihilates `f` in the anticommutator**, so it *cannot* change `b_k` — it only boosts the u-block.
Only a *non-commuting* `Λ` (vertex-diagonal, or the decoupling multiplier below) can cancel `b_k`.

## The f-coupling is CHEAP to repair (bounded multiplier)

The decoupling multiplier `Λ_dec` with `Λ_dec f = −(L−λ₂I)⁺Mf` cancels every `b_k` exactly (residual
`5·10⁻¹³`), leaving `M' = blockdiag(gap, M_uu)`. Crucially:

> **`‖Λ_dec‖₂ ~ n^{0.09}` (bounded, O(1))** on deg2+dense (median `0.98`, max `37` over the corpus).

So decoupling the Fiedler from the bulk costs only a **bounded** multiplier — the f-coupling is *not*
the source of the blow-up. (This is a structural surprise: one might expect the f-coupling to be the
problem; it is not.)

## The u-block is the obstruction (and it grows)

After decoupling, `M_uu` is *indefinite* (it inherits the large `−L_min` term, which on the dense
core has eigenvalues `~n²`). Boosting it to PSD:

| boost method | multiplier size on deg2+dense |
|---|---|
| `c·(L−λ₂I)⁺` (uniform `Π`) | `c* ~ n^{2.22}` |
| `α·(L−λ₂I)` (eigenvalue-weighted) | **`c* ~ n^{1.18}`** |

So the best structured certificate is **`Λ = Λ_dec + α(L−λ₂I)`** (bounded f-repair + eigenvalue-
weighted bulk boost), with size `~ n^{1.18}` — a genuine improvement over scalar (`n^{2.04}`) and
spectral `(L−λ₂I)⁺` (`n^{3.04}`), but **still unbounded**.

## deg2+dense scaling summary

| quantity | scaling | note |
|---|---|---|
| `gap` | `n^{−0.91}` | vanishes |
| `λ₃ − λ₂` (spectral gap above `f`) | `n^{1.73}` | **grows** — no near-degeneracy |
| `α*` (scalar) | `n^{2.04}` | exhausted |
| `c*` (spectral `(L−λ₂I)⁺`) | `n^{3.04}` | worse |
| **`‖Λ_dec‖`** (f-repair) | **`n^{0.09}`** | **bounded** |
| `c*` (decouple + uniform `Π`) | `n^{2.22}` | |
| **`c*` (decouple + scalar `α`)** | **`n^{1.18}`** | best structured |

All certificates are feasible per graph (566/566) — `gap ≥ 0` is true — but **none is uniformly
bounded**.

## Other families (subsumed)

- **Polynomial `Λ = aI+bL+cL²`** commutes with `L` ⇒ same class as scalar (cannot touch `b_k`); the
  bulk boost it provides is eigenvalue-weighted, identical in effect to `α(L−λ₂I)` on the u-block.
- **Low-rank projector onto `u₃,…,u_k`** / **block projection onto the dense core**: the negative
  direction of `M_uu` is a *high-frequency dense-core* mode (where `−L_min ~ −n²` lives); a projector
  onto it boosts exactly that direction, but the cost is `|λ_min(M_uu)|/(λ_k−λ₂) ~ n^{1.18}` — the
  same as the eigenvalue-weighted scalar. No saving.
- **Distance-to-carrier diagonal `Λ = diag(β)`**: a non-commuting diagonal *can* cancel `b_k` (like
  `Λ_dec`), but the residual u-block boost is unchanged; the diagonal that also boosts the core needs
  growing weights (consistent with the `c·D` test of the previous round, where `c` grew with `n`).

## Conclusion

- **The f-coupling `b_k` is cheaply repaired** by a *bounded* multiplier `Λ_dec` (`‖Λ_dec‖ ~ O(1)`) —
  decoupling the Fiedler from the bulk is not the obstruction.
- **The obstruction is the u-block indefiniteness** `M_uu`, inherited from `−L_min` on the dense core
  (eigenvalues `~ −n²`). Lifting it to PSD costs `~ n^{1.18}` (eigenvalue-weighted), which is the best
  structured certificate found — better than scalar (`n²`) but still unbounded.
- **No bounded structured dual certificate exists** on deg2+dense: `gap ~ n^{−0.9} → 0` while `M`'s
  off-Fiedler part has magnitude `~ n²`, and the constraint `(L−λ₂I)` (eigenvalues `~ n^{1.7}` there)
  cannot fully offset it without an `~ n^{1.18}` multiplier. The S-procedure / dual route is
  intrinsically lossy for this family.

The decisive structural takeaway: **the difficulty of B is not the Fiedler's coupling to the bulk
(O(1)), but the magnitude of the min-degree-weighted Dirichlet operator `L_min` on the dense core
relative to the vanishing gap.** A successful certificate must exploit cancellation *within* the
u-block (between `λ₂(D+A)` and `L_min` on the core), not a generic multiplier — i.e. the proof has to
use the specific structure of `M_uu`, not the constraint alone.

## Lean
No new exact identity this round (the search is over inequalities/multiplier scalings). The exact
facts used — `M·1 = 0`, `gap = fᵀMf`, the eigen-constraint `(L−λ₂I)f = 0` — are already implicit in
the formalised `B2prime_min_decomp`, `quadForm_adjMatrix_fiedler`, and
`aggregate_triangle_poincare_regular` (the regular certificate `α = d+λ₂−1`).
