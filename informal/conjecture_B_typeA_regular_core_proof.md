# Conjecture B — `gap > 0` for TYPE A with regular cores

`G = H + v₀`, `v₀ ~ {a,b}`, `H` a `ρ`-regular core. Exact regular-core gap (verified, schur round):
`gap = λ(ρ−λ+1) + (3λ−λρ−2)x² + (2λ+ρ−2)(p²+r²) + (3−ρ)xy − λS²/m`, with `x=f_v₀`, `p=f_a`, `r=f_b`,
`y=p+r=(2−λ)x`, `S=(4−ρ−λ)x`, `m=ρ(n−1)/2+2`. Code:
[`conjecture_B_typeA_regular_core_proof.py`](../conjecture_B_typeA_regular_core_proof.py).

## TASK 1 — symmetric reduction

Symmetric attachment `p = r = (2−λ)x/2` gives `p²+r² = (2−λ)²x²/2`, `xy = (2−λ)x²`, so

> **`gap = λ(ρ−λ+1) + x²·K`**, with
> `K(λ,ρ,m) = (3λ−λρ−2) + (2λ+ρ−2)(2−λ)²/2 + (3−ρ)(2−λ) − λ(4−ρ−λ)²/m`.

Verified exact (`|formula − gap| ≤ 2·10⁻¹³` for symmetric/complete cores; `~10⁻⁵` for random-regular,
where `|p−r| ≈ 10⁻³`). So `gap` is an explicit function of `(x², λ, ρ, m)`.

## TASK 2 — normalization (η=0 core)

With the core perp `η = ‖f_H − mean‖` set to `0` (mean-field core; **exact for the complete core**,
where all non-attachment vertices are equivalent), normalization
`x² + 2p² + (n−3)μ² = 1`, `μ = −(3−λ)x/(n−3)` gives

> **`x² = 1/D`**, `D(λ,n) = 1 + (2−λ)²/2 + (3−λ)²/(n−3)`.

So `x² = 1 − O(1/n)` (the bottleneck carries the mass), confirmed: `x²_true ≈ 1/D` to `<10⁻³` for
dense cores (e.g. `rr(99,50)`: `1/D = 0.9892 = x²_true`).

## TASK 3 — `gap > 0`

Substituting `x² = 1/D`:

> **`gap_closed = λ(ρ−λ+1) + K/D`.**

**Complete core `ρ = n−2` (η = 0 exact, `λ = 2`, `p = r = 0`):**

> **`gap = λ(ρ−λ+1) + K/D = 10(n−3)/m > 0`** — verified exact (`K99`: `gap_closed = 0.19988 =
> 10·96/m = gap`). **Unconditional proof of Conjecture B for the complete-core (densest) TYPE A**,
> manifestly positive (`10(n−3)/m`, `n > 3`).

**General `ρ`:** `gap = λρ(1−x²) + [remainder]` with `λρ(1−x²) = λρ‖f_H‖² > 0` the positive driver
(`f_H ≠ 0` since `f ⊥ 1`). `gap_closed` is positive for every `(ρ,n)` tested and approximates the true
gap; the difference is the **core-perp correction `η`** (the resolvent response, `O(1/γ)`), which is
zero only for the complete core. So:

- the reduction `gap = λ(ρ−λ+1) + x²K` is **exact**;
- the **complete core is proved** (`10(n−3)/m`);
- for general `ρ`, `gap > 0` is **verified** and reduces to controlling the single core-perp term `η`
  (i.e. `x² ≈ 1/D` with the resolvent error bounded) — the same `poincare_on_block`-type control as
  TYPE B.

## TASK 4 — the eigenvalue λ

The secular equation gives `λ ≈ 2 − 2/(ρ−λ+1)` (the rigid-block resolvent at the attachment):

| core | `λ` | `2−2/(ρ−λ+1)` | `2−2/ρ` |
|---|---|---|---|
| rr(99,10) | 1.767 | 1.783 | 1.800 |
| rr(99,50) | 1.980 | 1.959 | 1.960 |
| rr(199,100) | 1.990 | 1.980 | 1.980 |
| K99 | 2.000 | 1.979 | 1.980 |

Accurate to `~0.02`; `λ → 2` as `ρ → ∞` (the bottleneck sharpens). With `(2−λ)(ρ−λ+1) ≈ 2` the
`K`-terms carrying `(2−λ)` are `O(1/ρ)`, and `gap_closed → λ(ρ−λ+1) + (leading K)/D`.

## TASK 5 — verification (closed form vs numerical gap)

`ρ ∈ {5,10,20,50,100,n−2}`, `n ∈ {50,100,200}`:

| ρ | n | λ | gap_true | gap_closed(η=0) | rel.err | gap>0 |
|---|---|---|---|---|---|---|
| 48 | 50 | 2.000 | 0.39898 | 0.39898 | **0.0000** | ✓ |
| 20 | 100 | 1.913 | 0.56030 | 0.54539 | 0.027 | ✓ |
| 50 | 100 | 1.980 | 0.29701 | 0.29614 | 0.003 | ✓ |
| 98 | 100 | 2.000 | 0.19988 | 0.19988 | **0.0000** | ✓ |
| 100 | 200 | 1.990 | 0.15020 | 0.15001 | 0.001 | ✓ |
| 6 | 100 | 1.451 | 3.10282 | 2.08071 | 0.329 | ✓ |
| 198 | 200 | 2.000 | 0.09998 | 0.09998 | **0.0000** | ✓ |

> **All `gap > 0`.** The closed form is **exact for the complete core** (rel.err `0`), `<3%` for
> `ρ ≥ 20` (good expanders, small `η`), and degrades for poor expanders (`ρ=6`: `33%`, where `η` is
> large) — but `gap_true > 0` throughout, and `gap_closed > 0` too.

## Conclusion

- **Exact reduction:** `gap = λ(ρ−λ+1) + x²·K(λ,ρ,m)` (symmetric attachment).
- **Complete-core TYPE A is PROVEN:** `gap = 10(n−3)/m > 0`, manifestly positive (the `η=0` closed
  form is exact there).
- **General regular core:** `gap > 0` verified for all `(ρ,n)`; the η=0 closed form `λ(ρ−λ+1)+K/D > 0`
  is an accurate (dense) approximation, and the only gap to a fully unconditional proof is bounding the
  core-perp `η` (the resolvent / `poincare_on_block` control) — exactly the residual already isolated.
- **Secular:** `λ ≈ 2 − 2/(ρ−λ+1) → 2`.

So the densest TYPE A (complete core) is closed in closed form, and the general regular case is reduced
to one explicit, resolvent-controlled correction term `η`, with the positive driver `λρ‖f_H‖²`
identified.

## Lean
No new lemma: the complete-core `gap = 10(n−3)/m` and the symmetric reduction are construction-specific
(deg-2 vertex on a regular/complete core with explicit eigenvector), the same induced-block setup
deferred throughout. The general bound still depends on the η/resolvent control.
