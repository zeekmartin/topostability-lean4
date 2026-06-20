# Conjecture B — the joint cancellation `R″ + C_attach` and the `n/m` residual (TYPE A)

Deg-2 vertex `v₀` on core `H`. `x = f_v₀`, `y = f_a+f_b`, `λ = λ₂`, `d_a, d_b` = G-degrees of the
attachments, `m = |E|`, core mean `μ`, core perp `η`. Bottleneck: `(2−λ)x = y`. Code:
[`conjecture_B_typeA_joint_cancellation.py`](../conjecture_B_typeA_joint_cancellation.py).

## Exact pieces (verified, residual `≤9·10⁻¹⁴`)

> `C_attach = (d_a−2)f_a(f_a−x) + (d_b−2)f_b(f_b−x)`  (oriented to the higher-degree endpoints `a,b`);
> `fᵀDf = 2x² + d_a f_a² + d_b f_b² + Σ_{u∈C} d_u f_u²`;  `S = 2x + d_a f_a + d_b f_b + Σ_{u∈C} d_u f_u`;
> `(2−λ)x = y`  (the `v₀`-row of `Lf = λf`).

`R″ = λ(fᵀDf − λ + 1 − S²/m)`. Substituting the splits gives the exact joint expression
`R″ + C_attach`; on a regular core `C_dense ≈ 0` (`≤0.09`, only from `a,b` having degree `+1`), so
`gap = R″ + C_attach + C_dense`.

## Leading cancellation

With `x → ±1`, `f_a, f_b = O(1/γ)`, `μ = −x/(n−1)`, and `q = d̄_core/n`:

| term | leading value |
|---|---|
| `R″` | `2(1−q)·x²` |
| `C_attach` | `−2(1−q)·x²` |

(verified: e.g. `rr(400,200)`, `q=0.5`: `R″/x² = 1.063`, `|C_attach|/x² = 1.003`.) So **`R″_∞ + C_attach_∞ = 0`** — the `O(1)` parts cancel exactly, and `gap` is the **sub-leading residual**.

## The residual is a positive multiple of `n/m`

Testing the candidate forms (regular cores, `n = 100,200,400`, fractions `frac = d̄/n`):

| candidate | behaviour |
|---|---|
| `gap/((2−λ)x²)` | **not constant** (5.5, 9.9, 12.9, 28 for frac=0.2…0.7) and **diverges at q=1** (`2−λ=0`) — ✗ |
| `gap/core_var` | not constant (94 → 2485) — ✗ |
| `gap/(f_a−f_b)²` | not constant — ✗ |
| **`gap·m/n`** | **converges to `c(q)`** (frac 0.2→4.5, 0.3→6.45, 0.5→6.5, 0.7→~8) — ✓ |

> **`gap ≈ c(q)·n/m`**, `c(q) > 0` increasing with density: `≈4.5` (q=0.2) → `≈6.5` (q=0.5) → **`10`**
> (q=1). This **generalises the exact q=1 result `gap = 10(n−3)/m`** (`c = 10`).

So the positive sub-leading residual is a **multiple of `n/m`** (inverse average degree), *not* of
`(2−λ)`, the core variance, or `(f_a−f_b)²`. The `(2−λ)` candidate is decisively ruled out by the q=1
case (`2−λ = 0` yet `gap = 10(n−3)/m > 0`).

## Why `n/m` and not `(2−λ)`

`(2−λ)x = y` and `C_attach ≈ −(Δ−1)·y·x`, so `C_attach` carries the `(2−λ)` factor — but it is exactly
*cancelled* by the matching part of `R″` (both `= 2(1−q)x²`). What *survives* is the `−λ S²/m` term of
`R″` against the `Σ d_u f_u²` term: the residual is governed by the **edge count `m`** (through
`S²/m`), giving the `n/m` scaling. At q=1 this is the exact `10(n−3)/m`; the `(2−λ)`-carrying parts
vanish (`2−λ = 0`), confirming the residual lives in the `S²/m`/`m`-structure, not the spectral gap.

## Conclusion

- **Exact joint formula:** `R″ + C_attach` with `C_attach = (d_a−2)f_a(f_a−x)+(d_b−2)f_b(f_b−x)` and
  the `fᵀDf`, `S` splits; leading parts cancel (`R″_∞ = −C_attach_∞ = 2(1−q)x²`).
- **Positive residual form identified:** `gap ≈ c(q)·n/m`, `c(q) ∈ [4.5, 10]` increasing with
  density, `→ 10` at `q = 1` (where `gap = 10(n−3)/m` exactly). It is a positive multiple of `n/m`
  (the "`m`-/degree-expression" candidate), **not** of `(2−λ)`, core variance, or `(f_a−f_b)²`.
- **Manifest positivity** of `gap` reduces to `c(q) > 0` — still the conjecture for the general core
  (no closed form for `c(q)`), but the **form `gap = Θ(n/m)` is now pinned and consistent with the
  exact q=1 value `c = 10`**. The next concrete target is a *lower bound* `c(q) ≥ c₀ > 0`, i.e.
  `gap ≥ c₀·n/m` — a single scalar inequality replacing the failed leading-order separation.

## Lean
No new lemma: the exact pieces (`C_attach` formula, bottleneck `(2−λ)x=y`, `fᵀDf`/`S` splits) are
specific to the `G = H + v₀` construction (not general-graph identities), and the residual form
`gap = c(q)·n/m` is asymptotic. The only closed-form instance remains the exact q=1
`gap = 10(n−3)/m`.
