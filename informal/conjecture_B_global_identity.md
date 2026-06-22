# Conjecture B — search for a case-split-free global identity for `gap = λ₂G − T ≥ 0`

Goal: an exact global identity `gap = PositiveTerm + Residual` with `Residual ≥ 0` *structurally* (from
`Lf = λ₂f`), no case split, no local apex bounds. **Result: the clean global identity is
`gap = (λ·fᵀDf − T) − Required`. The positive term `λfᵀDf − T ≥ 0` is exactly the aggregate Poincaré
(holds 9/9), but the residual `−Required` is SIGN-VARYING — and its sign IS the regime boundary. No
case-split-free structurally-non-negative residual exists in this framework.** Code:
[`conjecture_B_global_identity.py`](../conjecture_B_global_identity.py).

## TASK 1 — the clean elimination from `Lf = λf`

`Af = (D − L)f = Df − λf`, hence

> **`fᵀA²f = ‖Af‖² = Σ_v (d_v − λ)² f_v²`** (verified to machine precision, all graphs).

This eliminates all two-step neighbour sums. **But `T` uses `A ⊙ A²` (the `t`-weighted adjacency,
`t_e = (A²)_{ab}` *restricted to edges*), not `A²` itself** — so this elimination does *not* simplify
`T`. The triangle structure (which edges carry which `t_e`) is not reachable from the eigenvector
equation alone; that is the irreducible combinatorial content.

## TASK 2 — the exact global identity

`gap = 2λfᵀDf − λ² − λS²/m − T`. Group as:

> **`gap = (λ·fᵀDf − T) − Required`**, where `Required = λ(λ + S²/m − fᵀDf)`.

(Check: `(λfDf − T) − λ(λ+S²/m−fDf) = 2λfDf − λ² − λS²/m − T = gap`.) Two clean global pieces.

## TASK 3/5 — sign analysis: the positive term is the aggregate Poincaré; the residual flips sign

| candidate | structurally `≥ 0`? |
|---|---|
| **`λfᵀDf − T`** (aggregate Poincaré slack) | **YES — 9/9** (min `0.087`); this is exactly `aggregate_triangle_poincare` (`T_ord ≤ 2λ·fᵀDf ⟺ T ≤ λfᵀDf`) |
| `−Required` | **NO — sign-varying** (`+` in regime i, `−` in regime ii) |
| `R1` (centered-apex residual `2λΣ(d−λ)²f²/d − λ² − λS²/m`) | NO — 3/9 |
| `Gram(f, Af) = ‖Af‖² − (fᵀAf)²` | always `≥ 0` (Cauchy–Schwarz) but **unrelated to `gap`** (`= Σ(d−λ)²f² − (fDf−λ)²`) |

> **The only clean global non-negative term is `λfᵀDf − T ≥ 0` (the aggregate Poincaré, the existing
> `aggregate_triangle_poincare` lemma).** The residual `−Required` is positive in regime i
> (`Required ≤ 0`) and *negative* in regime ii (`Required > 0`). So `gap = (≥0) − Required` is
> manifestly `≥ 0` **only when `Required ≤ 0`**.

## TASK 4 — exact values

| graph | gap | `Required` | `λfᵀDf − T` |
|---|---|---|---|
| K₂₀ | 0 | **+20** | 20 (`= Required`, saturated) |
| K₂₀ − e | 18 | 0 | 18 |
| rr(20,4) | 6.54 | **−2.95** | 3.58 (regime i: `gap = 3.58 + 2.95`) |
| cycle₃₀ | 0.17 | −0.086 | 0.087 |
| deg2+dense(40) | 3.29 | **+0.68** | 3.97 (regime ii: `gap = 3.97 − 0.68`) |

- **Regime i (`Required ≤ 0`: rr, cycle):** `gap = (λfDf−T) + |Required|` — *both terms non-negative*,
  `gap ≥ λfDf − T ≥ 0`. The aggregate Poincaré alone proves it.
- **Regime ii (`Required > 0`: K_n, deg2+dense, gnp):** `gap = (λfDf−T) − Required` — the aggregate
  slack must *exceed* `Required`. At `K_n` they are *equal* (`20 = 20`, `gap = 0`, saturation). For
  deg2+dense the slack `3.97 > 0.68` wins, but proving `λfDf − T ≥ Required` is exactly `gap ≥ 0`
  (circular).

## TASK 5 — why no case-split-free identity exists (this framework)

The exact identity `gap = (λfᵀDf − T) − Required` is the cleanest possible global decomposition, and it
shows the obstruction precisely:

1. **`λfᵀDf − T ≥ 0`** (aggregate Poincaré) is the clean structural PositiveTerm — and it is *itself*
   the open lemma `aggregate_triangle_poincare` (holds 9/9, proof open in general; regular case proved).
2. **`Required` changes sign**, and its sign is *exactly* the regime boundary. In regime i, `gap ≥
   λfDf − T ≥ 0` (aggregate suffices). In regime ii, `λ₂G < λfDf`, so `T ≤ λ₂G` is *strictly stronger*
   than the aggregate `T ≤ λfDf`, and the aggregate Poincaré is **insufficient** — `gap ≥ −Required`
   gives a *negative* lower bound.

So **the case split on `sign(Required)` is intrinsic to this decomposition** — not a choice but a
consequence: the global PositiveTerm (`λfDf − T`) dominates `gap` iff `Required ≤ 0`. A case-split-free,
structurally-non-negative residual would require a *different* PositiveTerm that already incorporates
the `−Required` correction — i.e. exactly `T ≤ λ₂G` itself (circular), since `λ₂G = λfDf − Required`.

## Conclusion

- **Exact global identity found:** `gap = (λfᵀDf − T) − Required`, `Required = λ(λ + S²/m − fᵀDf)`.
- **Clean elimination:** `fᵀA²f = Σ(d−λ)²f²` (from `Af = Df − λf`) — but it does not reach `T` (which
  uses `A ⊙ A²`), so the triangle combinatorics survive.
- **No case-split-free structurally-non-negative residual:** the only clean PositiveTerm is the
  aggregate Poincaré `λfDf − T ≥ 0`; the residual `−Required` flips sign at the regime boundary. In
  regime ii the aggregate is *insufficient* (`λ₂G < λfDf`), so `gap ≥ 0` there is not implied by any
  single global non-negative term short of `T ≤ λ₂G` itself.
- This **vindicates the regime split** as intrinsic (not a crutch): `Required`'s sign is forced by the
  decomposition. The aggregate Poincaré (`aggregate_triangle_poincare`) handles regime i; regime ii
  (`Required > 0`, includes the extremizer `K_n` and deg2+dense) genuinely needs the stronger
  `T ≤ λ₂G`, with no global identity reducing it further.

So the "last obstruction" (regime ii, `Required > 0`) is **not** removable by a global identity: it is
where the clean global PositiveTerm runs out, and `K_n` saturates it (`λfDf − T = Required`). Any proof
must address regime ii directly (the global-maximum-at-`K_n` statement), confirming the prior rounds'
conclusion that `gap ≥ 0` is irreducibly a global maximum, not a sum-of-squares.

## Lean
No new lemma. The identity `gap = (λfᵀDf − T) − Required` and `fᵀA²f = Σ(d−λ)²f²` are clean (the latter
from `Af = Df − λf`, formalizable). The decomposition confirms: `aggregate_triangle_poincare`
(`T ≤ λfᵀDf`) closes regime i; regime ii needs `triEnergy_le_RHS` (`T ≤ λ₂G`) directly, with `K_n` the
saturating case — no further global reduction.
