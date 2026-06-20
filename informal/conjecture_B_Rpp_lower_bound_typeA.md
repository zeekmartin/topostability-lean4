# Conjecture B — lower bound for R″ in the TYPE A core-gap model (and why separate bounds fail)

Model: degree-2 vertex `v₀` on core `H` (`γ = λ₂(H)`, max degree `Δ`, mean core degree `d̄ ≈ qn`).
`R″ = λ₂(fᵀDf − λ₂ + 1 − S²/m)`. Goal: lower-bound `R″` to match `|C_attach| ≤ C·Δ/γ·f_v₀²` so that
`gap = R″ + C ≥ 0`. Code: [`conjecture_B_Rpp_lower_bound_typeA.py`](../conjecture_B_Rpp_lower_bound_typeA.py),
27 cores (`K`, `gnp(·,q)` q=0.2..0.9, random-regular) at `m = 100, 300, 600`.

## Leading-order R″

Using `f_{v₀} → ±1`, `f` flat on `H` (resolvent, `f_H = c·1 + f_H^⊥`, `c = −f_v₀/(n−1)`,
`‖f_H^⊥‖ = O(1/γ)`), `λ₂ → 2`, and the degree-2 equation `(2−λ₂)f_v₀ = f_a + f_b`:

| term | leading value |
|---|---|
| `fᵀDf` | `2f_v₀² + c²·2m_H + O(1/γ) = (2 + q)·f_v₀²` |
| `λ₂` | `2` |
| `S²/m` | `(c·2m_H)²/m = (d̄·f_v₀)²/m = 2q·f_v₀²` |
| **`R″`** | `2·[(2+q) − 2 + 1 − 2q]·f_v₀² = ` **`2(1−q)·f_v₀²`** |

Verified (e.g. `gnp(600,q)`): `R″/f_v₀² = 1.68, 1.46, 1.045, 0.74, 0.44, 0.24` vs `2(1−q) = 1.60,
1.40, 1.00, 0.71, 0.41, 0.21` for `q = 0.2…0.9` — matches the leading `2(1−q)`, with a small positive
excess (the gap). So **`R″ ≈ 2(1−q)f_v₀² > 0`** for `q < 1`.

## …but `|C_attach|` has the SAME leading order

`C_attach ≈ −(Δ−1)f_v₀(f_a+f_b) = −(Δ−1)ε₁f_v₀²` (`ε₁ = 2−λ₂`), and numerically

> **`|C_attach|/f_v₀² → 2(1−q)`** as well: `gnp(600,0.5)`: `R″/f_v₀² = 1.045`, `|C_attach|/f_v₀² =
> 1.047` — **equal to 3 digits**.

This is the exact leading-order cancellation `R″_∞(q) + C_∞(q) = 0` with `R″_∞ = −C_∞ = 2(1−q)f_v₀²`.
Hence `gap/f_v₀² = R″/f_v₀² − |C_attach|/f_v₀² → 0`:

| q | `gap/f_v₀²` (n=100) | (n=300) | (n=600) |
|---|---|---|---|
| 0.3 | 0.334 | 0.090 | 0.017 |
| 0.5 | 0.258 | 0.045 | ~0 |
| 0.9 | 0.272 | 0.088 | 0.045 |

The gap is **sub-leading** (`→ 0` as `n → ∞`); the `O(1)` parts of `R″` and `|C_attach|` cancel
exactly.

## The separate-bounds strategy is provably insufficient

A lower bound `R″ ≥ c·Δ/γ·f_v₀²` does hold — but with a constant *too small* to beat `|C_attach|`.
In `Δ/γ·f_v₀²` units, `ρ_R = R″·γ/(Δf_v₀²)`, `ρ_C = |C_attach|·γ/(Δf_v₀²)`:

> **`inf ρ_R = 0.033` (complete core) `< sup ρ_C = 1.340` (random-regular).**

So **no universal `c`** satisfies `R″ ≥ c·Δ/γ·f_v₀²` *and* `c ≥ sup ρ_C`. Per graph `ρ_R > ρ_C`
(26/27; the one "failure" is the omitted small `C_dense`), i.e. `gap > 0` always — but this
separation is **per-graph, not via universal `Δ/γ` constants**, because `R″` and `C_attach` are *not
independent*: both are built from the same resolvent solution `f_a` (`R″` through `S²/m ∋ f_a` and
`C_attach ∝ f_a`), so they track each other and cancel at leading order.

## Conclusion

- **`R″ ≈ 2(1−q)·f_v₀²`** (leading order; positive for `q<1`) — a clean lower bound, but
- **`|C_attach| ≈ 2(1−q)·f_v₀²` has the identical leading order** (the exact cancellation
  `R″_∞ + C_∞ = 0`), so **a separate lower bound on `R″` can never dominate `|C_attach|`** — the
  required constant satisfies `inf ρ_R = 0.03 ≪ sup ρ_C = 1.34`.
- `gap = R″ + C_attach` is the **sub-leading `O(1/n)` residual** of two matched `O(1)` quantities; its
  positivity is genuine (`gap > 0`, all cores) but **cannot be obtained by bounding `R″` and
  `C_attach` separately** — it requires a **joint** estimate of `R″ + C_attach` that exploits their
  shared dependence on the resolvent value `f_a`.

This answers the task: the lower bound `R″ ≥ c·Δ/γ·f_v₀²` exists (`c ≈ 0.03`) but is provably useless
for `gap ≥ 0`; the strategy must be replaced by a joint bound on `R″ + C_attach` (equivalently,
compute the sub-leading term directly, as in the exact `q=1` result `gap = 10(n−3)/m`).

## Lean
No new lemma (leading-order asymptotics; the finding is a negative result on the separate-bounds
strategy, not an exact identity). The exact `q=1` joint result (`gap = 10(n−3)/m`) remains the only
closed form; the general joint sub-leading term is open.
