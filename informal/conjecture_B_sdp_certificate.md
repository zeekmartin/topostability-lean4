# Conjecture B — S-procedure / Lagrange certificate for `C + R″ ≥ 0`

Reduced target: `gap := λ₂G − B2′ = C + R″ ≥ 0` for `f` with `Lf = λ₂f`, `f ⊥ 1`. Write it as a
quadratic form `gap = fᵀMf` with the explicit symmetric matrix

> **`M = λ₂(D+A) − (λ₂/m)·ddᵀ − L_min`**,  `L_min` = Laplacian with edge weights `min(d_a,d_b)−1`.

Verified `fᵀMf = gap` and **`M·1 = 0`** (residual `2·10⁻¹²` — `M` is calibrated to annihilate
constants). The constraint `(L−λ₂I)f = 0` lets us add any multiplier vanishing on `f`: for a scalar
`α`, `M_α := M + α(L−λ₂I)` has `fᵀM_α f = gap`. **If `M_α ⪰ 0` on `1⊥`, then `gap ≥ 0`.** Code:
[`conjecture_B_sdp_certificate.py`](../conjecture_B_sdp_certificate.py), 566 graphs.

## TASK 5 — regular graphs: an exact clean certificate

For a `d`-regular graph, `L_min = (d−1)L`, `Q = 2dI − L`, `ddᵀ = d²·11ᵀ`, so

> `M = 2λ₂d·I − (λ₂+d−1)·L − (2λ₂d/n)·11ᵀ`, and with **`α = d + λ₂ − 1`**:
> **`M_α = λ₂(d+1−λ₂)·I − (2λ₂d/n)·11ᵀ`**, i.e. `M_α|_{1⊥} = gap·I = λ₂(d+1−λ₂)·I ⪰ 0`.

Verified exactly (C₂₀, Petersen, K₈, Q₄, K₃,₃): `M_α|_{1⊥}` is the scalar matrix `gap·I`. This is a
**clean S-procedure proof of B for regular graphs** (the multiplier `α = d+λ₂−1` collapses `M_α` to a
nonnegative multiple of the identity), equivalent to the formalised `aggregate_triangle_poincare_regular`.

## TASK 1/2 — scalar certificate: always feasible, but not uniform

| quantity | value |
|---|---|
| scalar certificate feasible (some finite `α`) | **566/566** |
| `α*` (min feasible) | min 1.4, median 19, max 479 |
| `α*/(Δ+λ₂−1)` | median **0.97**, max 7.99 |
| explicit `α = Δ+λ₂−1` certifies | 309/566 (55%) |
| explicit `α = 2Δ` certifies | 444/566 (78%) |
| explicit `α = d̄+λ₂−1` certifies | 202/566 |

A scalar certificate **always exists** (as it must, since `gap ≥ 0` and `L−λ₂I ⪰ 0` on `1⊥` with
kernel `f` — a Schur-complement argument gives feasibility for large `α`). Typically `α* ≈ Δ+λ₂−1`
(the regular formula with `d → Δ`), but no single explicit closed form is universal: even `2Δ` fails
on 22%.

## TASK 4 — deg2+dense: the multiplier blows up

| n | gap | `α*` | Δ | PSD at `α=Δ+λ₂−1`? |
|---|---|---|---|---|
| 10 | 2.35 | 3.7 | 7 | yes |
| 20 | 1.34 | 12.8 | 14 | yes |
| 50 | 0.53 | 96.4 | 37 | **no** |
| 100 | 0.35 | 330 | 76 | **no** |
| 200 | 0.15 | 1696 | 148 | **no** |

> **`α* ~ n^{2.04}`** — the required multiplier grows *super-linearly*, far faster than any natural
> graph parameter (`Δ ~ n`). The explicit `α = Δ+λ₂−1` (which works for small n) **fails for n ≥ 50**.

So on the asymptotically tight family the scalar S-procedure is **lossy**: `gap ~ n^{−0.9} → 0` while
`α* ~ n²`. Heuristically `α* ~ b²/(gap·(λ₃−λ₂))` (Schur complement), and with `gap → 0` and a small
spectral gap `λ₃−λ₂`, the multiplier explodes. The certificate exists per graph but has no uniform
description.

## TASK 3 — diagonal multiplier `Λ = c·D`

`M + c(D(L−λ₂I) + (L−λ₂I)D)` (anticommutator, vanishes on `f`) PSD on `1⊥` for some `c∈[0,3]`:
**479/566** (better than the explicit scalar). But on deg2+dense the needed `c` grows
(`0.45 → 0.65 → 0.75` for `n = 20,50,100`), so the diagonal multiplier is **also not uniform**.

## Conclusion

- **Regular: a clean exact S-certificate** `α = d+λ₂−1 ⟹ M_α|_{1⊥} = λ₂(d+1−λ₂)·I` (re-proves the
  formalised regular case in S-procedure form — the multiplier turns `M_α` into a nonnegative scalar
  matrix).
- **A scalar certificate always exists** (566/566), with `α* ≈ Δ+λ₂−1` typically — but **no uniform
  closed form**: explicit `Δ+λ₂−1` certifies only 55%, `2Δ` 78%.
- **The S-procedure is lossy at scale.** On deg2+dense `α* ~ n²` blows up (`gap ~ n^{−0.9}`), so
  neither a scalar nor a simple diagonal (`c·D`) multiplier is uniform. This mirrors the variational
  round (the dual): minimality / S-procedure with a low-complexity multiplier cannot certify the
  near-cancelling `O(n^{−0.9})` gap.
- **What remains:** a *structured matrix* multiplier `Λ(G)` (not scalar/`c·D`) whose entries track the
  bottleneck, or a non-multiplier argument. The regular `α = d+λ₂−1` is the only clean closed-form
  certificate; the irregular bottleneck (deg2+dense) is where every low-complexity certificate fails.

## Lean
No new exact identity formalised this round. The one clean exact statement — the regular S-certificate
`M_α|_{1⊥} = λ₂(d+1−λ₂)·I` (`α = d+λ₂−1`) — restates the already-formalised
`aggregate_triangle_poincare_regular`; formalising it as a matrix identity would require defining `M`
(hence `L_min`, `ddᵀ`) with no new mathematical content. The negative scaling result (`α* ~ n²`) is
empirical, not an identity.
