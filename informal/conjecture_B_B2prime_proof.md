# Conjecture B — exact decomposition of the triangle-free B2′ slack

Target (triangle-free, degree-only): **`B2′ = Σ_e w_e g_e² ≤ λ₂·G`**, `w_e = min(d_a,d_b)−1`,
`g_e = f_a−f_b`, `h_e = f_a+f_b`, `G = Σ_e h_e² − S²/m = Σ_e(h_e−h̄)²`, `S = Σ_v d_v f_v = Σ_e h_e`.
Code: [`conjecture_B_B2prime_proof.py`](../conjecture_B_B2prime_proof.py).

## The exact slack decomposition

Using `min(a,b) = ½(a+b) − ½|a−b|`:

> `B2′ = ½Σ_e(d_a+d_b)g_e² − ½Σ_e|d_a−d_b|g_e² − Σ_e g_e²`
> `   = ⟨d,Γ(f)⟩ − N − λ₂`,  `N := ½Σ_e|d_a−d_b|g_e² ≥ 0`, `Σg² = λ₂`.

(degree-*average* Dirichlet `⟨d,Γ⟩ = ½Σ(d_a+d_b)g²` minus degree-*discrepancy* gradient `N` minus
the base Dirichlet `λ₂`.) With `⟨d,Γ⟩ = λ₂fᵀDf − ½𝒜` (`𝒜 = Cov_L(d,f²)`), the slack is (verified,
residuals `≤2·10⁻¹²`):

> **`λ₂G − B2′ = R″ + C`**,  where
> `R″ = λ₂·(fᵀDf − λ₂ + 1 − S²/m)`  (spectral term),
> `C = Σ_{e: h higher-deg endpoint} (d_h − d_l)·f_h·(f_h − f_l)`  (oriented lower→higher-degree edge sum),

and the per-edge collapse `C = N + ½𝒜` (residual `2·10⁻¹³`): the two `O(n)` pieces `N` and `½𝒜`
combine to the `O(1)` oriented sum `C`. So **`B2′ ≤ λ₂G ⟺ R″ + C ≥ 0 ⟺ −C ≤ R″`.**

## Regular graphs = the equality base case

For a regular graph all degrees are equal, so `d_h = d_l` on every edge: `C = N = 𝒜 = 0`. Then

> `λ₂G − B2′ = R″ = λ₂(fᵀDf − λ₂ + 1 − S²/m) = λ₂(d + 1 − λ₂)`  (`S=0`, `fᵀDf=d`),

which is `≥ 0` since `λ₂ ≤ d+1`, with **equality exactly at `K_n`** (`λ₂ = d+1 = n`). Verified:

| graph | C | N | 𝒜 | gap | `R″` | `λ₂(d+1−λ₂)` |
|---|---|---|---|---|---|---|
| C₂₀ | 0 | 0 | 0 | 0.284 | 0.284 | 0.284 |
| Petersen | 0 | 0 | 0 | 4.000 | 4.000 | 4.000 |
| Q₄ | 0 | 0 | 0 | 6.000 | 6.000 | 6.000 |
| K₈ | 0 | 0 | 0 | 0.000 | 0.000 | 0.000 |

So the irregular slack `R″ + C` is the regular base `R″` plus the degree-gradient correction `C`,
which switches on exactly when degrees are non-uniform. This is the formalised
`aggregate_triangle_poincare_regular` (`C = 0` case).

## Sign structure and the open step

| quantity | value |
|---|---|
| `R″ ≥ 0` | `512/566` (`R″` min `−0.080` — *not* always ≥ 0) |
| `C < 0` | `423/566` (`C` mostly negative) |
| `−C/R″` (where `R″ > 0`) | max `0.79`, median `0.23` |
| `R″ + C ≥ 0` (the conjecture) | `566/566` |

`R″` is *not* always nonnegative and `C` is *not* always one sign, so the inequality is a genuine
balance: the spectral term `R″` must dominate the (usually negative) degree-gradient `C`. The single
remaining open step is **`−C ≤ R″`**, i.e.

> `Σ_{e: h higher-deg}(d_h − d_l)·f_h·(f_l − f_h) ≤ λ₂(fᵀDf − λ₂ + 1 − S²/m)`.

## deg2+dense: the asymptotic gap is a near-cancellation, not one positive term

On deg2+dense (the asymptotically tight family), the gap `~ n^{−0.9}` is **not** a single positive
term — it is the small difference of two `O(1)` terms:

| n | gap | `R″` | `C` | `N` | `𝒜/2` |
|---|---|---|---|---|---|
| 50 | 0.528 | 1.170 | −0.642 | 24.8 | −25.4 |
| 200 | 0.145 | 0.816 | −0.671 | 123.7 | −124.4 |
| 1000 | 0.037 | 0.722 | −0.685 | 641.7 | −642.4 |
| 2000 | 0.018 | 0.711 | −0.693 | 1285.2 | −1285.9 |

Fits: `R″ ~ n^{−0.13}` (→ `≈0.71`), `C ~ n^{0.03}` (→ `≈−0.69`), while `N, 𝒜/2 ~ n^{1.05}`
(huge, cancelling to the `O(1)` `C = N + 𝒜/2`). So **the gap is `R″ + C`, a near-cancellation of the
spectral term (`→0.71⁺`) against the oriented degree-gradient (`→−0.69⁻`)**; their `O(n^{−0.9})`
residual is the margin. A proof must control this delicate balance — the degree-discrepancy pieces
`N`, `𝒜` are individually `O(n)` and only their `C`-collapse is `O(1)`.

## Is the slack a weighted variance?

No single manifest weighted variance: `R″` carries the centered-lift variance signature (the `−S²/m`
term), but `C` is a *sign-indefinite* oriented covariance between degree-gradient `(d_h−d_l)` and the
Fiedler product `f_h(f_h−f_l)`. The slack is `variance-flavoured spectral term + signed degree–Fiedler
covariance`, not a sum of squares — the same global (non-SOS) obstruction as every prior route, now
in the sharpest triangle-free, degree-only form.

## Conclusion

- **Exact:** `λ₂G − B2′ = R″ + C`, `R″ = λ₂(fᵀDf−λ₂+1−S²/m)`, `C = Σ_{e}(d_h−d_l)f_h(f_h−f_l)`
  (oriented to the higher-degree endpoint) `= ½Σ|d_a−d_b|g² + ½Cov_L(d,f²)`.
- **Regular = equality base case:** `C = N = 𝒜 = 0`, `gap = R″ = λ₂(d+1−λ₂)`, `=0` at `K_n`
  (formalised).
- **deg2+dense:** gap is the `O(n^{−0.9})` near-cancellation of `R″ → 0.71` and `C → −0.69` (not one
  positive term); `N, 𝒜` are `O(n)` and collapse to the `O(1)` `C`.
- **Open step (single, triangle-free):** `−C ≤ R″`, i.e. the spectral term dominates the oriented
  degree-gradient. `R″` is not always `≥0`, `C` not one-signed — a genuine balance requiring Fiedler
  minimality.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `B2prime_min_decomp` — `Σ[i∼j](min(d_i,d_j)−1)(f_i−f_j)² = ½Σ(d_i+d_j)(f_i−f_j)² −
  ½Σ|d_i−d_j|(f_i−f_j)² − Σ(f_i−f_j)²` (the exact min-weight / edge-variance decomposition of B2′,
  via `min(a,b) = ½(a+b)−½|a−b|`; algebraic, no spectral hypothesis). The slack identity
  `λ₂G − B2′ = R″ + C` then follows by combining this with `quadForm_adjMatrix_fiedler`
  (`⟨d,Γ⟩ = λ₂fᵀDf − ½𝒜`) and `degAssort_covariance`; the regular case is
  `aggregate_triangle_poincare_regular`.
