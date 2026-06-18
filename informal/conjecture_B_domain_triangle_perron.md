# Conjecture B — domain-local triangle-weighted Poincaré (Perron / Collatz–Wielandt)

Sole focus: the domain-local inequality that the reduction in
[`conjecture_B_same_sign_reservoir.md`](conjecture_B_same_sign_reservoir.md) leaves open. On a
single nodal domain `D` (one sign of `f`), set `x_v = |f_v| ≥ 0`. With internal triangle weights
`W_ab = t_ab` (`ab∈E(D)`), `τ_v^D = Σ_{u∈D,u∼v} t_{vu}`, full degree `d_v`:

> `T_D = Σ_{ab∈E(D)} t_ab(x_a−x_b)² = xᵀ(diag(τ^D) − W_D)x`,  `C_same_D = 2Σ_{ab∈E(D)} t_ab x_a x_b`.

**Target:** `T_D ≤ λ₂·Σ_{v∈D} d_v x_v²`  (⇔ `C_same_D ≥ Σ_{v∈D}(τ_v^D − λ₂ d_v)x_v²`).

Code: [`conjecture_B_domain_triangle_perron.py`](../conjecture_B_domain_triangle_perron.py).
**1168 nodal domains** (corpus + barbell/glue/chain-clique families).

**Headline.** The target holds on every domain (`T_D/[λ₂Σd x²] ≤ 0.738`, comfortable). But the
three natural Perron-style closures **all fail for concrete, documented reasons**: `x=|f|` is
*special*, not extremal, so the inequality is not a spectral fact about the triangle-weighted
operator — it lives on the single vector pinned by the global eigen-equation. The clean exact
identity that survives is the **triangle-level row equation** `A²f = A D f − λ₂(D−λ₂)f`
(formalised); the obstruction to using it is the **Hadamard gap** between the operator `A²` and
the triangle weight `M = A∘A²`.

---

## TASK 1 & 2 — Rayleigh quotient and the spectrum of the weighted operator

`T_D ≤ λ₂·Σ_D d_v x_v²` is the generalized Rayleigh inequality `xᵀL^t_D x ≤ λ₂·xᵀD_D x`, where
`L^t_D = diag(τ^D) − W_D` is the **triangle-weighted Laplacian** on `D` and `D_D = diag(d_v)`
(full degrees).

| quantity | min | median | max |
|---|---|---|---|
| `λ_D/λ₂` where `λ_D = T_D/Σ_D d_v x_v²` | 0.000 | 0.052 | **0.738** |
| `T_D ≤ λ₂Σd x²` holds | — | — | **1168/1168** |
| generalized `μ_max(L^t_D, D_D)/λ₂` | 0.00 | **1.46** | **12755** |
| domains with `μ_max > λ₂` | — | — | **653/1168 (56%)** |

**The inequality is NOT spectral.** The largest generalized eigenvalue of `(L^t_D, D_D)` exceeds
`λ₂` in 56% of domains (up to `12755×`): there exist vectors `y` with `yᵀL^t_D y ≫ λ₂ yᵀD_D y`.
So `T_D ≤ λ₂Σd x²` cannot follow from any bound on the operator pair — it holds **only because
`x=|f|` avoids the high directions of `L^t_D`**. Any proof must use what pins `x`: the global
eigen-equation. `λ_D ≤ 0.738λ₂` confirms the actual margin is large (the global ratio→1 tightness
was an artefact of clique-energy subtraction; it is gone here).

## TASK 3 — is `x=|f|` Perron / sub- / super-solution for `W_D`?

No. The coordinatewise ratio `(W_D x)_v / x_v` has median spread (std) `26.3` — `x` is **nowhere
near** an eigenvector of the triangle adjacency `W_D`. It is a uniform sub-solution
(`W_D x ≤ ρ(W_D)x`) in only `217/1168` domains (and super-solution in the same `217`, i.e. only
when it happens to be a near-eigenvector). **Perron–Frobenius on `W_D` does not apply** to `x`.

## TASK 4 — the row equation induced by the eigen-equation (EXACT, formalised)

`Lf = λ₂f` ⇒ `Af = (D−λ₂)f` (`A = adjMatrix`, `D = degMatrix`, `L = D−A`). Restricted to `D`
(where `f_v = x_v > 0` and opposite-domain neighbours have `f_u < 0`):

> **`A_D x = (D − λ₂)x + b`**,  `b_v = Σ_{u∉D,u∼v}|f_u| ≥ 0`  (boundary inflow). (residual `4·10⁻¹⁴`)

So `L_D^{Dir} x = λ₂x − b ≤ λ₂x` pointwise (`L_D^{Dir} = D_{full} − A_D`, the **Dirichlet
Laplacian**): `x` is a Collatz–Wielandt **sub-solution** for the *unweighted* domain operator.
This is the proved unweighted reservoir bound `2Σ_{E(D)}x_a x_b ≥ Σ_D(d_v−λ₂)x_v²`.

Lifting to the triangle level, squaring `Af = (D−λ₂)f` gives the exact identity

> **`A² f = A D f − λ₂(D − λ₂)f`**  (residual `8·10⁻¹³`; formalised as `adjSq_mulVec_fiedler`).

Entrywise `(A²)_{vu} = |N(v)∩N(u)|`, so this is the triangle-level row equation. **But** the
triangle energy uses the **Hadamard** weight `M = A∘A²` (common neighbours of *adjacent* pairs),
whereas `A²` is the full operator: `(A²f)_v` mixes the wanted `Σ_{u∼v}t_{vu}f_u` with a
**2-path term** `Σ_{u≁v}(\#\text{common nbrs})f_u`. The 2-path term has no eigen-equation, so the
clean operator recursion does **not** restrict to the triangle-weighted sum. This Hadamard gap is
the precise reason the weighted inequality resists the unweighted machinery.

## TASK 5 — pointwise Collatz–Wielandt (sufficient, but FALSE by a hair)

If `L^t_D x ≤ λ₂ D_D x` held **pointwise**, then `x_v ≥ 0` and summing would give the target for
free. Pointwise this is `Σ_{u∈D,u∼v} t_{vu}(x_v − x_u) ≤ λ₂ d_v x_v`.

> **Pointwise holds in `1161/1168` domains — it FAILS in 7.** Failures are `7` vertices out of
> `20 876`, all **low-degree** (median degree `5` vs `25`) with moderate `x` (`x/x_max ≈ 0.35`).
> Worst relative violation `+0.45`.

So Collatz–Wielandt-by-pointwise-domination is **too strong**: a handful of low-degree vertices
break it, yet their `x_v·r_v` weight is negligible so the quadratic form survives. The inequality
is **genuinely aggregate** — it cannot be localised to per-vertex domination.

## Conclusion — what closes it, what does not

| strategy | verdict |
|---|---|
| generalized eigenvalue bound `μ_max(L^t_D,D_D) ≤ λ₂` | **dead** — `μ_max/λ₂` up to `12755`; `x` is special |
| Perron–Frobenius on `W_D` (`x` an eigenvector / sub-sol) | **dead** — `x` is not close to a `W_D`-eigenvector |
| pointwise Collatz–Wielandt `L^t_D x ≤ λ₂D_D x` | **dead by a hair** — fails at `7/20876` low-degree vertices |
| aggregate `xᵀL^t_D x ≤ λ₂ xᵀD_D x` (the target) | **true, 1168/1168, margin ≤ 0.738** |

The target is true and well-clear of tight, but it is irreducibly an **aggregate** statement about
the *single* vector `x=|f|` fixed by the global eigen-equation — not a spectral property of the
triangle-weighted operator, and not localisable to vertices. The exact bridge to triangles is the
formalised recursion `A²f = ADf − λ₂(D−λ₂)f`; the open gap is the **Hadamard** restriction from
`A²` to `M = A∘A²` (dropping 2-path terms), which is exactly what the eigen-equation does not see.

**Next lever (not a closed route):** combine the apex identity `T_D = Σ_c E_{G[N(c)∩D]}(x)` with
the *global* (not per-apex) eigen-equation, summing the triangle-level recursion over apices so the
2-path terms cancel in aggregate — i.e. prove the aggregate directly from `A²f=ADf−λ₂(D−λ₂)f`
rather than per-vertex or per-apex.

## Formalised (Lean, `ConjectureB.lean`)
- `adjSq_mulVec_fiedler` — the exact triangle-level row equation `A²f = A·Df − λ(Df − λf)` for any
  Laplacian eigenpair `(λ,f)`. No `sorry`, no graph hypotheses beyond the eigen-equation.
