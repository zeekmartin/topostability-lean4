# Conjecture B — is the open-2-path energy a Bochner / Γ₂ term?

Setup (combinatorial `L = D − A`, `Lf = λ₂f`, `f` unit Fiedler). Carré du champ and iterated
carré du champ (Bakry–Émery, graph version):

> `Γ(f)(v) = ½Σ_{u∼v}(f_v−f_u)²`,  `Γ₂(f)(v) = ½[LΓ(f)(v) − 2Γ(f,Lf)(v)] = ½(LΓ(f))(v) − λ₂Γ(f)(v)`
> (eigenvector), `Γ(f,g)(v) = ½Σ_{u∼v}(f_v−f_u)(g_v−g_u)`.

Target (`= −Q ≥ 0`): `Open + 𝒜 ≥ λ₂fᵀAf`, `𝒜 = Cov_L(d,f²)`, `fᵀAf = fᵀDf − λ₂`. Code:
[`conjecture_B_bochner_open_paths.py`](../conjecture_B_bochner_open_paths.py), 580 graphs, all
residuals machine-zero.

---

## TASK 1/2 — exact identities

All verified at machine zero (580 graphs):

| identity | residual |
|---|---|
| `Σ_v Γ(f)(v) = fᵀLf (= λ₂)` | `4·10⁻¹⁴` |
| `Σ_v Γ₂(f)(v) = −λ₂²` (integrated Bochner: `= −‖Lf‖²` in this sign convention) | `5·10⁻¹³` |
| `⟨d,Γ(f)⟩ = ½Σ_{ab∈E}(d_a+d_b)(f_a−f_b)²` (degree-weighted Dirichlet energy) | `7·10⁻¹²` |
| `𝒜 = 2λ₂·fᵀDf − 2⟨d,Γ(f)⟩` | `0` |
| **pointwise Bochner** `L(f²) = 2λ₂·f² − 2Γ(f)` | `7·10⁻¹⁴` |

The pointwise identity is the eigenvector case of the **carré-du-champ product rule**
`L(f²) = 2 f·Lf − 2Γ(f)` (algebraic, no spectral hypothesis — the graph Leibniz rule). It is the
engine: averaging against `d` turns the covariance correction `𝒜` into a degree-weighted carré du
champ.

### The Bochner form of the conjecture

Substituting `𝒜 = 2λ₂fᵀDf − 2⟨d,Γ⟩` into `−Q = Open + 𝒜 − λ₂fᵀAf` gives (residual `6·10⁻¹³`):

> **`−Q = Open + λ₂·fᵀDf + λ₂² − 2⟨d,Γ(f)⟩`**, hence
> **Conjecture B ⟺ `2⟨d,Γ(f)⟩ ≤ Open + λ₂·fᵀDf + λ₂²`.**

The LHS `2⟨d,Γ(f)⟩ = Σ_{ab∈E}(d_a+d_b)(f_a−f_b)²` is the **degree-weighted Dirichlet energy**; the
conjecture says it is dominated by the open-2-path energy plus two spectral terms.

## TASK 3 — Open is *not* below the curvature term; it dominates the excess

| quantity | value |
|---|---|
| `Open / ⟨d,Γ(f)⟩` | min `0.43`, median `1.75`, max `1.98` |
| `Open ≤ ⟨d,Γ(f)⟩` | only `35/580` |
| curvature excess `E = 2⟨d,Γ⟩ − λ₂fᵀDf − λ₂²` | min `−0.22`, max `489` |
| `Open ≥ E` ( `= −Q ≥ 0`, the conjecture ) | **580/580** |

So `Open` is *not* a sub-term of `⟨d,Γ⟩` (it is ~1.75× larger typically). The conjecture is the
clean statement `Open ≥ E`: the open energy clears the **curvature excess** `E = 2⟨d,Γ⟩ −
λ₂fᵀDf − λ₂²` (which is itself sometimes negative ⇒ trivial).

## TASK 4 — Open is the *incomplete-neighbourhood* term, not a Γ₂ value

**Per-vertex `Γ₂` is not the open energy.** Pooled correlations of `Γ₂(f)(x)` with local features:

| feature | corr |
|---|---|
| `−λ₂·Γ(f)(x)` (= `λ₂·γ_x`, sign) | `−0.885` |
| `λ₂·f_x²` | `−0.562` |
| `D_x` (closed neighbour-pair energy) | `−0.489` |
| `O_x` (**open** neighbour-pair energy) | `+0.193` |

`Γ₂(f)(x)` is dominated by `−λ₂Γ(f)(x)` and the closed/curvature structure; the open-pair term
`O_x` is only weakly present. **So `Open` is not a per-vertex `Γ₂` quantity**, and no `Γ₂` aggregate
equals it (`Σ_vΓ₂ = −λ₂²`, `⟨d,Γ₂⟩` has no clean tie to `Open`).

**But `Open` *is* exactly the apex non-adjacent-neighbour-pair energy** (residual `5·10⁻¹¹`):

> `Σ_x O_x = 2·Open`,  `O_x = Σ_{y,z∈N(x), y≁z}(f_y−f_z)²` (ordered).

i.e. `Open = Σ_{induced P₃}(f_a−f_b)²` is the **incompleteness of neighbourhoods**: it vanishes iff
every `N(x)` is a clique (chordal/locally-complete), matching
[`conjecture_B_A2_triangle_gap.md`](conjecture_B_A2_triangle_gap.md).

### Where this sits in the graph-Bochner literature

On graphs the iterated carré du champ `Γ₂(f)(x)` expands over the local structure, and its lower
bound (the curvature-dimension condition `CD(K,n)` / `CDE`) is governed by the **triangles through
`x`**: pairs of neighbours `y,z` that *are* adjacent (`y∼z`, closed cherries) raise curvature; pairs
that are *not* adjacent (`y≁z`, open cherries) are the curvature **deficit**.

- **Bakry & Émery (1985)** — Γ-calculus, `CD(K,∞)`.
- **Lin & Yau (2010)**, *Ricci curvature and eigenvalue estimate on locally finite graphs* — graph
  `CD` condition; `Γ₂` involves the 2-ball of `x`.
- **Jost & Liu (2014)**, *Ollivier's Ricci curvature, local clustering and curvature-dimension
  inequalities on graphs* — makes the link explicit: **local clustering (triangles) raises Ricci
  curvature; the absence of triangles among the neighbours (the open cherries) is exactly the
  curvature deficit.** This is the precise conceptual home of `Open`.
- **Bauer–Horn–Lin–Lippner–Mangoubi–Yau (2015)**, *Li–Yau inequality on graphs* (the `CDE`
  condition) — the graph chain-rule failure is corrected through the carré du champ; the same
  neighbour-pair structure governs the exponential curvature-dimension bound.

So the finite-graph statement "open-2-path energy = the contribution from non-adjacent neighbour
pairs" is the **clustering/chordality deficit** in the graph Bochner formula: `Open` is the
aggregate over apices of the non-triangle neighbour pairs — the very term that degrades graph Ricci
curvature when neighbourhoods are not cliques.

## Conclusion

- `Open` is **not** a `Γ₂`/Bochner *value* (per-vertex or aggregate): `Γ₂(f)(x) ≈ −λ₂Γ(f)(x) +
  (curvature)`, `Σ_vΓ₂ = −λ₂²`, none equal `Open`.
- The Bochner machinery instead recasts the **correction**: `L(f²) = 2λ₂f² − 2Γ(f)` gives `𝒜 =
  2λ₂fᵀDf − 2⟨d,Γ⟩`, so **Conjecture B ⟺ `2⟨d,Γ(f)⟩ ≤ Open + λ₂fᵀDf + λ₂²`** — the degree-weighted
  Dirichlet energy is dominated by the open energy plus spectral terms.
- `Open` *is* exactly the **incomplete-neighbourhood (non-adjacent neighbour pair) energy**, which is
  the **curvature-deficit / clustering** term in the graph Bochner formula (Jost–Liu). A working
  proof should therefore couple the degree-weighted carré du champ `⟨d,Γ(f)⟩` to this clustering
  deficit — a graph Bochner/`Γ₂` estimate with the triangle (clustering) term retained.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `lapMatrix_mulVec_sq` — `(L(f∘f))_v = 2·f_v·(Lf)_v − Σ_{u∼v}(f_v−f_u)²`: the carré-du-champ
  product rule `L(f²) = 2 f·Lf − 2Γ(f)` (algebraic). At an eigenvector this is the Bochner identity
  `L(f²) = 2λ₂f² − 2Γ(f)` underlying `𝒜 = 2λ₂fᵀDf − 2⟨d,Γ(f)⟩`.
