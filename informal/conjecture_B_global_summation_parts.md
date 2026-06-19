# Conjecture B — global summation-by-parts and the covariance form of the correction

Target (equivalent to the conjecture; `−Q ≥ 0`, verified 580/580 in
[`conjecture_B_hub_correction.md`](conjecture_B_hub_correction.md)):

> **`Open + 𝒜 ≥ λ₂·fᵀAf`**,  i.e.  `Open + 𝒜 − λ₂fᵀAf = −Q ≥ 0`,

with `Open = fᵀL_P f ≥ 0` (open-2-path Dirichlet energy), `𝒜 = Σ_{ab∈E}(d_a−d_b)(f_a²−f_b²)`
(degree–Fiedler assortativity), `A` the adjacency matrix (`fᵀAf = fᵀDf − λ₂` for unit `f`), and
`Q = T − λ₂fᵀDf` the aggregate slack. This note runs the **global summation-by-parts** search
requested: which exact identities does the eigen-equation `Lf = λ₂f` generate that connect `Open`,
`𝒜`, `λ₂fᵀAf`, and the degree-weighted energies? Code:
[`conjecture_B_global_summation_parts.py`](../conjecture_B_global_summation_parts.py), 580 graphs,
all residuals machine-zero.

---

## 0. The one structural fact that organises everything

For **any** symmetric operator `B` and the Fiedler eigenvector `f` (`Lf = λ₂f`, `L`, `B` symmetric),

> **`fᵀB L f = (Bf)ᵀ(Lf) = λ₂(Bf)ᵀf = λ₂·fᵀBf`.**

So *every* "multiply `Lf=λ₂f` by the operator-image `(Bf)_v` and sum" identity is a **tautology** —
one application of the eigen-equation, no new content. In particular the two routes proposed in the
task collapse exactly (verified, residual `≤2·10⁻¹⁰`):

| suggested SBP | reduces to |
|---|---|
| `fᵀM L f` | `λ₂·fᵀMf` |
| `fᵀL A² f` | `λ₂·fᵀA²f` |
| `fᵀL_P f`, `fᵀL_M f`, `fᵀ(AD+DA)Lf` | `λ₂·fᵀ(·)f` |

**New content can only come from expanding one side combinatorially** (edge / 2-path sums) before
the eigen-equation is used, or from a non-tautological *bilinear* pairing. Those are PARTS A–B.

## PART A — the assortativity correction is a graph covariance  (NEW, exact, formalised)

Writing `f∘f` for the entrywise square (a *vector*), the bilinear Dirichlet form of the Laplacian
between the degree vector `d` and `f∘f` is exactly the correction:

> **`𝒜 = ⟨d, f∘f⟩_L := dᵀL(f∘f) = ½ Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)`**   (residual `1.3·10⁻¹²`).

This is the **covariance of degree and squared-Fiedler value** in the graph-Laplacian inner product.
Equivalent exact forms verified: `𝒜 = (f∘f)ᵀL d = Σd²f² − dᵀA(f∘f) = −Σ_v(σ_v−d_v²)f_v²`. The
"load-bearing hub mass" of all previous notes is therefore not an ad-hoc edge antisymmetry — it is a
single covariance functional, `Cov_L(d, f²)`, which is **≤ 0 exactly when degree and `f²` are
anti-monotone across edges** (the hub-flatness signature, `𝒜 ≤ 0` on `504/580`).

Formalised in `ConjectureB.lean` (no `sorry`):
- `lapMatrix_bilin` — `uᵀLw = Σ_{i,j}[i∼j]u_i(w_i−w_j)` (the bilinear Dirichlet form, any `u,w`);
- `degAssort_covariance` — `dᵀL(f∘f) = ½Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)` (= `𝒜`).

## PART B — the edge↔diagonal SBP family  (multiply by `w_v f_v`)

The genuinely non-tautological summation-by-parts: multiply the **row equation**
`(Af)_v = (d_v−λ₂)f_v` by a degree-weighted scalar `w_v f_v` and sum. The left side is an *edge*
correlation, the right side a *degree diagonal*:

> **`Σ_{ab∈E}(w_a+w_b)f_a f_b = Σ_v w_v(d_v−λ₂)f_v²`**   (exact for every `w`; residual `≤2·10⁻¹⁰`).

| `w` | identity | status |
|---|---|---|
| `1` | `fᵀAf = Σ(d−λ₂)f²` | known (`quadForm_adjMatrix_fiedler`) |
| `d` | `fᵀADf = Σ d(d−λ₂)f²` | **NEW** (`quadForm_deg_adjMatrix_fiedler`) |
| `d²`| `Σ_E(d_a²+d_b²)f_af_b = Σ d²(d−λ₂)f²` | exact |
| `σ` | `Σ_E(σ_a+σ_b)f_af_b = Σ σ(d−λ₂)f²` | exact |

These are the *complete* "degree-weighted multiplier" content of the eigen-equation. They turn every
degree-weighted edge sum into a one-line diagonal — but note the LHS lives on **edges** while `Open`
lives on **non-edges** (2-paths through a shared neighbour), so this family alone never touches
`Open`. Formalised: `quadForm_deg_adjMatrix_fiedler` (`w=d`).

## PART C — the target, covariance-reframed

Combining PART A with `λ₂fᵀAf = λ₂(fᵀDf − λ₂)` (`quadForm_adjMatrix_fiedler`):

> **`−Q = Open + Cov_L(d, f²) − λ₂(fᵀDf − λ₂)`**   (residual `7.4·10⁻¹²`),

equivalently the clean **open-energy lower bound**

> **`Open ≥ λ₂(fᵀDf − λ₂) − Cov_L(d, f²)`.**

The right side is now two interpretable global scalars: a spectral term `λ₂·fᵀAf ≥ 0` and the
degree–`f²` covariance. The conjecture says the open-2-path energy clears the spectral demand
*minus* the covariance credit.

## PART D — no fixed-operator Rayleigh certificate

Treating the *actual* eigenvalue `λ₂` as a constant, `−Q = fᵀ(λ₂D − L_M)f` (definitionally,
`T = fᵀL_M f`). One could hope `B_λ := λ₂D − L_M ⪰ 0` (a graph-independent-of-`f` Rayleigh proof).
It is **false**:

> `λ_min(B_λ)`: min `−6240`, median `−229`;  `B_λ ⪰ 0` on only `2/580` graphs (near-regular).

So `−Q ≥ 0` is **special to the Fiedler direction** — it must use `λ₂ = fᵀLf` (the Rayleigh
identity couples the eigenvalue back into the vector), not just the scalar value of `λ₂`. This is
the operator-level statement of why every "bound a fixed quadratic form" route has failed.

## PART E — Cauchy–Schwarz on the covariance (a lead, not a closure)

Because `𝒜 = ⟨d, f²⟩_L` is a genuine inner product, Cauchy–Schwarz gives (verified `580/580`):

> `|𝒜| ≤ √( E_L(d)·E_L(f²) )`,  `E_L(g) = gᵀLg = Σ_{ab∈E}(g_a−g_b)²`,

with tightness `|𝒜|/√(…)` median `0.35` (max `1.00`). This bounds the correction by the Dirichlet
energies of `d` and of `f²`. But `E_L(f²) = Σ_{ab∈E}(f_a−f_b)²(f_a+f_b)²` is an **edge** energy,
whereas `Open` is a **non-edge** 2-path energy — different index sets — so Cauchy–Schwarz does not
directly couple `𝒜` to `Open`. (Lead: a *2-path* Cauchy–Schwarz pairing `d` against `f²` over the
open cherries, matching `Open`'s support, is the only way this becomes a closure.)

## PART F — `−Q` has no degree-weighted 2-path sum-of-squares

The only exact rewrites of `−Q` are **circular**: `−Q = Open − Σ_v R_v f_v²` (signed `R`-diagonal,
residual `6·10⁻¹²`) and `−Q = fᵀ(λ₂D−L_M)f`. No degree-difference-weighted 2-path Dirichlet form
makes `−Q` manifestly nonnegative — confirming, at the operator level, the non-localisation found in
[`conjecture_B_open2path_gap.md`](conjecture_B_open2path_gap.md) and
[`conjecture_B_hub_correction.md`](conjecture_B_hub_correction.md). The negative covariance mass
(`Cov_L(d,f²) < 0` on hubs) must cancel `Open` *globally*.

## Conclusion

The summation-by-parts search is **exhausted on the edge/vertex side** and yields one genuinely new
structural object:

- **`𝒜 = Cov_L(d, f²)`** — the correction is the graph covariance of degree and squared Fiedler
  value (PART A, formalised). The target is `Open ≥ λ₂fᵀAf − Cov_L(d, f²)`.
- The **edge↔diagonal SBP family** `Σ_E(w_a+w_b)f_af_b = Σ w(d−λ₂)f²` is the complete degree-weighted
  multiplier content (PART B, `w=d` formalised); it never reaches `Open` (edge vs non-edge support).
- All **operator-product** SBP routes (`fᵀMLf`, `fᵀLA²f`, …) are tautologies `λ₂fᵀBf` (PART C/0).
- `B_λ = λ₂D − L_M` is **not PSD** (PART D): no fixed-operator Rayleigh certificate; the proof must
  use `λ₂ = fᵀLf`, not the scalar.
- The remaining gap is structural and unchanged: couple the **non-edge** energy `Open` to the
  **edge** covariance `Cov_L(d,f²)`. The eigen-equation is an edge/vertex recursion and cannot
  bridge edge↔non-edge; the one untried lever is a **2-path Cauchy–Schwarz** pairing `d` against
  `f²` over the open cherries (PART E), which alone matches `Open`'s support.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `lapMatrix_bilin` — `uᵀLw = Σ_{i,j}[i∼j]u_i(w_i−w_j)` (Laplacian bilinear/Dirichlet form).
- `degAssort_covariance` — `dᵀL(f∘f) = ½Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)`: the correction `𝒜` is
  the degree–`f²` Laplacian covariance.
- `quadForm_deg_adjMatrix_fiedler` — `(Df)ᵀ(Af) = Σ_v d_v(d_v−λ₂)f_v²`: the `w=d` edge↔diagonal SBP
  identity.
