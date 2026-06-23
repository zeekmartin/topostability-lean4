# Conjecture B — the matrix-power route (the Hadamard obstruction, made precise)

Exploit `T = fᵀL_t f` (`L_t = diag(σ) − A²⊙A`) and `Af = (D−λ)f` to express `T` via powers of `A` at
`f`. **Result: the exact identities hold (`T = Σ_v σ_v f_v² − fᵀ(A²⊙A)f`, `fᵀA²f = Σ(d_v−λ)²f_v²`,
`(A³)_vv = σ_v`), but the triangle energy is IRREDUCIBLE to matrix powers: `fᵀ(A²⊙A)f` (and `T`, `Σσf²`)
do NOT lie in the span of `{fᵀA²f, fᵀA³f, Σdᵏf², λ}` (best-fit relative residual 0.12). The Hadamard
masking `A²⊙A` is not a polynomial in `A`; `fᵀA²f`/`fᵀA³f` stay `O(1)` at `K_n` while `T = O(n²)` —
scale-decoupled. This is the precise reason every algebraic route (`B2′`, `W`, `F`, matrix powers) failed.**
Code: [`conjecture_B_matrix_power_route.py`](../conjecture_B_matrix_power_route.py).

## TASK 1/3 — exact identities (all verified `< 10⁻¹²`)

| identity | meaning | err |
|---|---|---|
| `T = fᵀL_t f` | `L_t = diag(σ) − A²⊙A`, `σ_v = Σ_{u∼v}t_{vu}` | `2·10⁻¹³` |
| `T = Σ_v σ_v f_v² − fᵀ(A²⊙A)f` | split: triangle-degree term − Hadamard | `2·10⁻¹³` |
| `fᵀA²f = Σ_v(d_v−λ)²f_v²` | `‖Af‖² = ‖(D−λ)f‖²` (clean vertex sum) | `1·10⁻¹³` |
| `(A³)_vv = σ_v` | triangle degree = closed 3-walks | `0` |

## TASK 2 — `fᵀA³f` is an edge sum, not a vertex sum

`fᵀA³f = (Af)ᵀA(Af) = gᵀAg` with `g = (D−λ)f`, so
`fᵀA³f = Σ_{a,b}A_{ab}(d_a−λ)(d_b−λ)f_af_b = 2·Σ_{a∼b}(d_a−λ)(d_b−λ)f_af_b`. This is an **edge sum**
(needs the graph structure), NOT a pure vertex degree-power sum. So even `fᵀA³f` does not reduce to
`{Σdᵏf², Σdᵏf, λ}`. The clean reduction stops at `fᵀA²f = Σ(d−λ)²f²` (`k=2`); `k ≥ 3` re-introduces
edge/neighbour products.

## TASK 4 — `T` does NOT reduce to matrix powers (Hadamard irreducible)

Best linear fit (least squares across the corpus) of each quantity to the basis
`{fᵀA²f, fᵀA³f, Σd²f², Σd³f², d_eff, λ, 1}`:

| quantity | relative residual |
|---|---|
| `fᵀ(A²⊙A)f` (Hadamard) | **0.121** |
| `T = Σσf² − fᵀ(A²⊙A)f` | **0.106** |
| `Σ_v σ_v f_v²` | **0.086** |

> Residuals `≫ 0` ⟹ **none of `T`, `fᵀ(A²⊙A)f`, `Σσf²` lies in the span of the matrix-power / degree
> basis**. The Hadamard product `A²⊙A` (mask `A²` to edges) is not a polynomial in `A` — the masking is
> the irreducible obstruction. `fᵀA²f = Σ(d−λ)²f²` is clean but **decoupled** from `T`.

## TASK 5 — scale decoupling kills any matrix-power bound

At `K_n`: `fᵀA²f = (d−λ)²·‖f‖² = ((n−1)−n)² = 1`, `fᵀA³f = fᵀAf·(stuff) = d_eff − λ = −1` — both `O(1)`.
But `T_unord = (n−2)·λ = O(n²)`. So `T` outgrows `fᵀA²f`, `fᵀA³f` by `Θ(n²)`:

| graph | `T` | `2λ·d_eff` | `fᵀA²f` | `fᵀA³f` | `Σσf²` |
|---|---|---|---|---|---|
| `K₃₀` | 840 | 1740 | 1.0 | −1.0 | 812 |
| deg2+dense(60,.9) | 3.7 | 11.5 | 43.8 | 2198 | 43.9 |

> `T` tracks `Σσf²` (the triangle-degree term), NOT `fᵀA²f`/`fᵀA³f` (which are `O(1)` at `K_n` and
> *huge* on deg2+dense — wildly mis-scaled vs `T`). **No bound of the form `T ≤ α·fᵀA²f + β·fᵀA³f + …`
> can hold** with fixed `α,β`.

## Conclusion

- **Exact identities hold** (`T = Σσf² − fᵀ(A²⊙A)f`, `fᵀA²f = Σ(d−λ)²f²`, `(A³)_vv = σ_v`).
- **The triangle energy is IRREDUCIBLE to matrix powers** (`fᵀ(A²⊙A)f`, `T`, `Σσf²` all off the
  matrix-power/degree span, residual ~0.1; `fᵀA³f` itself is an edge sum). The Hadamard masking is the
  obstruction.
- **`fᵀA²f`/`fᵀA³f` are scale-decoupled from `T`** (`O(1)` vs `O(n²)` at `K_n`), so no matrix-power bound
  on `T` exists.
- **This is the unified reason all algebraic routes failed** (`B2′`, `W`, `F`, min-degree, matrix powers):
  triangle counting is Hadamard, not polynomial in `A`. Only the *weighted* eigenspace form
  (`λD − L_t ⪰ 0 on E_{λ₂}`, `aggregate_triangle_slack_global.md`) captures it — the irreducible spectral
  core.

## Lean
No code change: the matrix-power route is a dead end (Hadamard irreducible, scale-decoupled). The clean
identity `fᵀA²f = Σ(d−λ)²f²` is true but does not bound `T`. `aggregate_triangle_poincare` stays the
direct sorry; the route forward remains the eigenspace-PSD `λD − L_t ⪰ 0 on E_{λ₂}` (the triangle
Laplacian `L_t` is genuinely Hadamard, not a polynomial in `A`). 3 sorrys unchanged.
