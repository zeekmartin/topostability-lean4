# Conjecture B — deep literature search: Hodge Laplacians + Mathlib

Two targeted searches: (1) does the Hodge-Laplacian literature give an interlacing
that proves `λ₂(T(G)) ≤ λ₂(G)`? (2) what does Mathlib4 already provide?

**Bottom line.** (1) Conjecture B sits naturally in the Hodge framework as
*"1-up spectral gap ≤ 1-down spectral gap"*, but **no published result gives a
cross-dimension / up-vs-down Fiedler bound** — known Hodge spectral theorems are
either *fixed-dimension under operations* (Horak–Jost interlacing) or *subcomplex
monotonicity* (neither implies B). (2) Mathlib4 has the graph-Laplacian basics and
the *global* Rayleigh sup/inf-is-an-eigenvalue results, but **lacks** `λ₂` as a
named quantity, the constrained Courant–Fischer min–max, eigenvalue interlacing,
and Loewner-order eigenvalue monotonicity.

---

## Search 1 — Hodge Laplacians

### The connection (made precise)
On the clique complex (vertices, edges, triangles) with boundary maps `B₁`
(vertex–edge `= ∂`) and `B₂` (edge–triangle):
- `L₀ = B₁B₁ᵀ` = **graph Laplacian** `L_G`; `λ₂(G)` = its smallest nonzero eigenvalue.
- `L₁ = L₁^down + L₁^up`, with `L₁^down = B₁ᵀB₁`, `L₁^up = B₂B₂ᵀ`.
- **Classical (Horak–Jost):** the nonzero spectra satisfy `s(Lᵢ^up) = s(Lᵢ₊₁^down)`.
  In particular `s(L₀) = s(L₁^down)` nonzero, so
  **`λ₂(G) = smallest nonzero eigenvalue of `L₁^down`**.
- Our triangle graph `T(G)` is the **unsigned/combinatorial up-adjacency** of edges
  via triangles, i.e. the combinatorial analogue of `L₁^up = B₂B₂ᵀ`. (Our identity
  `L_t = B·L_{T(G)}·Bᵀ` is the unsigned analogue of `L₀^{?}`-type relations.)

So **Conjecture B (`λ₂(T(G)) ≤ λ₂(G)`) is the combinatorial form of
*"smallest nonzero eigenvalue of `L₁^up` ≤ smallest nonzero eigenvalue of
`L₁^down`"* — i.e. the 1-up gap ≤ the 1-down gap.** This is a comparison between
the two halves of the Hodge 1-Laplacian, living on orthogonal Hodge subspaces
(`im B₂` vs `im B₁ᵀ`).

### Numerical check of the *signed* Hodge form
Computing `λ_min⁺(L₁^up = B₂B₂ᵀ)` vs `λ₂(G)` (signed Hodge) and vs `λ₂(T(G))`
(unsigned), the **signed Hodge form `λ_min⁺(L₁^up) ≤ λ₂(G)` holds**, and is
**tighter** than the combinatorial `λ₂(T(G)) ≤ λ₂(G)`:

| graph | λ₂(G) | λ_min⁺(L₁^up) | λ₂(T(G)) |
|---|---|---|---|
| `K₆` | 6.00 | 6.00 | 6.00 |
| `K₈−e` | 6.00 | **6.00 (=, tight)** | 5.00 |
| octahedron | 4.00 | 2.00 | 2.00 |
| `deg2+dense` (n≈24) | 1.96 | **1.91 (≈0.97·λ₂)** | 0.91 |

The signed 1-up gap nearly saturates `λ₂(G)` on the hard family (and equals it for
`K₈−e`), whereas the unsigned `λ₂(T(G))` keeps a margin. So the *signed* Hodge
"1-up ≤ 1-down" is the sharper conjecture; B (unsigned) is the looser companion.

### Is it known? — No.
- **Horak–Jost, "Spectra of combinatorial Laplace operators on simplicial
  complexes"** ([arXiv:1105.2712](https://arxiv.org/abs/1105.2712), Adv. Math. 2013):
  gives the framework and `s(Lᵢ^up)=s(Lᵢ₊₁^down)`, normalized eigenvalues in
  `[0,i+2]`. **No** comparison of the `L₁^up` gap to `λ₂(G)`.
- **Horak–Jost, "Interlacing inequalities for eigenvalues of discrete Laplace
  operators"** ([arXiv:1111.1836](https://arxiv.org/abs/1111.1836), Ann. Glob. Anal.
  Geom. 2013): all interlacing is at a **fixed dimension** under operations
  (deletion of a subcomplex, collapse, contraction, coverings, simplicial maps).
  **Confirmed: there is NO dimension-shift interlacing** and no bound of a
  higher-dimensional Fiedler value by a lower-dimensional one.
- **"Spectral monotonicity of the Hodge Laplacian"**
  ([arXiv:2304.00901](https://arxiv.org/abs/2304.00901)): for `K ⊆ G` subcomplexes,
  Hodge eigenvalues are monotone (padded-left). This is **subcomplex** monotonicity,
  not up-vs-down or cross-dimension — does not apply.
- **Lim, "Hodge Laplacians on graphs"**
  ([arXiv:1507.05379](https://arxiv.org/abs/1507.05379), SIAM Review 2020):
  foundational survey (cohomology, Hodge decomposition `im B₂ ⊕ ker L₁ ⊕ im B₁ᵀ`).
  States the structure but **no spectral-gap comparison** `L₁^up` vs `L₀`.
- Related (no applicable bound): [random walks / normalized Hodge 1-Laplacian,
  arXiv:1807.05044](https://arxiv.org/abs/1807.05044); [eigenvalue bounds for
  combinatorial Laplacians, arXiv:2510.25083](https://arxiv.org/abs/2510.25083).

**Verdict:** the Hodge framework gives the right *language* (B = 1-up gap ≤ 1-down
gap) and the classical `s(L₀)=s(L₁^down)` identity, but **no theorem proves the
up-vs-down gap comparison**. It is exactly the kind of cross-Hodge-subspace bound
that the literature does not address — consistent with all our direct attempts.

---

## Search 2 — Mathlib4 (declarations confirmed to compile on Modal)

`#check`-verified present (`Mathlib.Combinatorics.SimpleGraph.LapMatrix`,
`Mathlib.Analysis.InnerProductSpace.Rayleigh`):

**Graph Laplacian:**
- `SimpleGraph.lapMatrix` (`L = D − A`), `SimpleGraph.degMatrix`;
- `SimpleGraph.posSemidef_lapMatrix` (PSD);
- `SimpleGraph.lapMatrix_toLinearMap₂'` (`xᵀLx = ½ Σ_{i∼j}(xᵢ−xⱼ)²`);
- `..._eq_zero_iff_forall_adj` / `..._forall_reachable`;
- `SimpleGraph.lapMatrix_ker_basis`,
  `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`
  (kernel dimension = # connected components).

**Rayleigh quotient (global extrema only):**
- `ContinuousLinearMap.rayleighQuotient`;
- `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` /
  `..._iInf_...` (the **global** sup/inf of the Rayleigh quotient is an eigenvalue);
- `IsSelfAdjoint.hasEigenvector_of_isMaxOn` / `isMinOn` / `isLocalExtrOn`;
- `Matrix.PosSemidef` (PSD predicate; building block for a Loewner order).

**Missing in Mathlib (would be needed for a B proof):**
- **`λ₂` / algebraic connectivity** as a named quantity (the constrained
  `min_{x⊥1} Rayleigh`). Mathlib has only the *global* `⨅ x, rayleigh` (= smallest
  eigenvalue, which for `L_G` is `0`), **not** the second eigenvalue / min over
  `1^⟂`.
- **Courant–Fischer / min–max** for the `k`-th eigenvalue (only global sup/inf
  exist).
- **Eigenvalue interlacing** (Cauchy interlacing for compressions/principal
  submatrices) — absent.
- **Loewner-order eigenvalue monotonicity** (`A ⪯ B ⇒ λᵢ(A) ≤ λᵢ(B)`) — absent.
- Any **Hodge / higher Laplacian** or **triangle-graph** spectral API — absent.

**Implication for formalization.** The repo already has `triangleGraph`, `edgeLift`,
and the Lean-verified algebraic lemmas (`edgeLift_eval`, `edgeLift_diff_triangle`,
`triCount_le_*`). To formalize the lift route one would first need to *build* the
missing spectral infrastructure: a `λ₂`/algebraic-connectivity definition as a
constrained min, the `min_{x⊥1} Rayleigh = λ₂` characterization, and Cauchy
interlacing for the Ritz compression. None of this exists yet — it is a substantial
prerequisite, not a quick lemma lookup.

---

## Synthesis

- **Hodge placement (new framing):** Conjecture B is the combinatorial shadow of
  the **signed** Hodge inequality `λ_min⁺(L₁^up) ≤ λ₂(G) = λ_min⁺(L₁^down)` (1-up gap
  ≤ 1-down gap), numerically true and *tighter* than B itself. This is the cleanest
  statement of the conjecture, but it is **not a known theorem** — the Hodge
  literature offers only fixed-dimension interlacing and subcomplex monotonicity.
- **Mathlib status:** the graph-Laplacian PSD/quadratic-form/kernel API and global
  Rayleigh extrema exist; the `λ₂` min–max, interlacing, and Loewner machinery do
  **not**. A formal proof needs that infrastructure built first.
- **Net:** no off-the-shelf result (Hodge or Mathlib) cracks B; the deepest
  available context is the Hodge up-vs-down gap comparison, which is open in the
  same way our direct attempts found.

### Sources
- [Horak–Jost, Spectra of combinatorial Laplace operators (arXiv:1105.2712)](https://arxiv.org/abs/1105.2712)
- [Horak–Jost, Interlacing inequalities for discrete Laplace operators (arXiv:1111.1836)](https://arxiv.org/abs/1111.1836)
- [Spectral monotonicity of the Hodge Laplacian (arXiv:2304.00901)](https://arxiv.org/abs/2304.00901)
- [Lim, Hodge Laplacians on graphs (arXiv:1507.05379)](https://arxiv.org/abs/1507.05379)
- [Schaub et al., random walks & normalized Hodge 1-Laplacian (arXiv:1807.05044)](https://arxiv.org/abs/1807.05044)
- [Mathlib4: SimpleGraph.LapMatrix](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/LapMatrix.html),
  [InnerProductSpace.Rayleigh](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Rayleigh.html)

### Caveats
- Hodge↔T(G) correspondence is up to the signed/unsigned distinction (`L₁^up=B₂B₂ᵀ`
  signed vs `L_{T(G)}` combinatorial); the signed-form numerics are a small sample
  (illustrative). Mathlib declaration existence was confirmed by `#check` compiling
  on Modal (`lake env lean`).
