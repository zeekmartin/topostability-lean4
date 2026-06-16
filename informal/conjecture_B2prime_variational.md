# Conjecture B2′ — variational / second-variation attack on `C ≥ −R″`

B2′ ⟺ `C ≥ −R″`, with `C = Σ_{ab∈E}(d_h−d_l)·f_h·(f_h−f_l)` (h=higher-degree
endpoint) and `R″ = λ₂(fᵀDf − λ₂ + 1 − S²/m)`, `S=Σ_v d_v f_v`, `m=|E|`. The slack
`target := C + R″ = RHS − W₁ ≥ 0`. Code:
[`conjecture_B2prime_variational.py`](../conjecture_B2prime_variational.py).

**Headline (two negative-but-decisive results).**
1. **`R″ ≥ 0` is *not* an easy lemma.** It is equivalent to `fᵀN f ≥ 0` with
   `N := mA + mI − ddᵀ`, and `N` is **indefinite on `1⊥`** (PSD on only 6/9020
   graphs, min eigenvalue **−72**). Worse, `uᵢᵀN uᵢ ≥ 0` **fails on 44% (30952/69688)
   of the higher `L`-eigenvectors** — it holds *only* for the eigenvector of the
   **smallest** nonzero eigenvalue. So `R″ ≥ 0` requires the **minimality** of `λ₂`
   (Courant–Fischer), not merely the eigen-equation `Lf=λ₂f`. It is in the *same
   difficulty class* as B2′ itself, not a separable first step.
2. **`C + R″` is not the second variation of any natural degree-built perturbation.**
   All four candidate vectors `g₁…g₄ ⊥ {1,f}` give energies `gᵢᵀ(L−λ₂)gᵢ` that are
   **negatively correlated** with `target` (corr −0.39…−0.66); the best single fit and
   the full linear span both give **R² < 0** (worse than predicting the mean). The
   constructive variational route via these vectors **fails**.

---

## TASK 1 — `R″ ≥ 0`

**Reformulation (exact).** Using `fᵀAf = fᵀDf − λ₂` (from `Lf=λ₂f`) and `‖f‖²=1`:

> `R″ ≥ 0  ⟺  m(fᵀAf + 1) ≥ S²  ⟺  fᵀN f ≥ 0`,  `N := mA + mI − ddᵀ`,

since `m·R″/λ₂ = m(fᵀDf−λ₂+1) − S² = fᵀN f`. Verified: `R″ ≥ 0` on **9020/9020**
(equality exactly at `K_n`, where `N ≡ 0` on `1⊥`). A clean combinatorial form of `S`:
`S = Σ_v d_v f_v = Σ_{ab∈E}(f_a+f_b)`, and the eigen-equation gives the per-vertex
identity `Σ_{e∋v}(f_a+f_b) = (2d_v − λ₂)f_v`.

**Is it pure linear algebra? No.** `N = mA + mI − ddᵀ` is **indefinite on `1⊥`**:
PSD on only 6/9020 graphs, `λ_min(N|_{1⊥})` median **−36.6**, min **−72**. So
`fᵀN f ≥ 0` is *not* a matrix-PSD fact — it holds because `f` is a special vector.

**Does the eigen-equation suffice, or is minimality needed?** Testing `uᵢᵀN uᵢ` for
*every* `L`-eigenvector `uᵢ` (`i≥2`, each obeys `Auᵢ=(D−λᵢ)uᵢ`):
**fails on 30952/69688 (44%)** of them. Since it holds for `i=2` on every graph but
fails for many `i≥3`, the proof must use that `λ₂` is the **smallest** nonzero
eigenvalue (its Rayleigh-minimality), not just the eigen-equation. The "`+1`" is
exactly tuned: at `K_n`, `fᵀAf=−1`, so the bound is `0 ≥ 0` (tight).

**Plain Cauchy–Schwarz is too weak.** `S = ⟨1_E, Bᵀf⟩` gives only
`S² ≤ m·‖Bᵀf‖² = m(2fᵀDf − λ₂)`, overshooting the target `m(fᵀAf+1)=m(fᵀDf−λ₂+1)`
by `m(fᵀDf−1) = m·Σ_v(d_v−1)f_v² ≥ 0`. Equivalently `R″≥0 ⟺ ‖h′‖² ≥ fᵀDf−1` where
`h′ = Bᵀf − (S/m)1_E ⊥ 1_E`; the trivial `‖h′‖²≥0` is exactly `m(fᵀDf−1)` short.

**Lean-friendly statement (sub-lemma, still open).** For the unit Fiedler `f ⊥ 1`
of connected `G`:
> `(Σ_v d_v f_v)² ≤ |E| · (Σ_v d_v f_v² − λ₂ + 1)`,  i.e.  `fᵀ(mA+mI−ddᵀ)f ≥ 0`.

A proof needs Courant–Fischer minimality of `λ₂`. **Mathlib pieces:** present —
`SimpleGraph.lapMatrix`, `posSemidef_lapMatrix`, `lapMatrix_toLinearMap₂'`
(`xᵀLx=½Σ(xᵢ−xⱼ)²`), `ContinuousLinearMap.rayleighQuotient`,
`IsSymmetric.hasEigenvalue_iInf` (global inf). **Absent (must be built):** `λ₂` as a
*constrained* minimum over `1⊥` (`λ₂ = inf_{g⊥1} gᵀLg/‖g‖²`) — the Courant–Fischer /
Rayleigh characterization restricted to `1⊥`, which is the key tool and is not yet in
Mathlib under any name.

---

## TASK 2 — second-variation candidates

For any `g ⊥ 1`, `gᵀ(L−λ₂)g ≥ 0` (Rayleigh minimality on `1⊥`). If `C+R″` equalled
`gᵀ(L−λ₂)g` for an explicit `g`, B2′ would be **proved**. Candidates, projected onto
`{1,f}⊥`:

| `g` | `E=gᵀ(L−λ₂)g ≥ 0` | corr(E,target) | R²(`c·E`) | affine R² |
|---|---|---|---|---|
| `g₁ = Df` | 9020/9020 | **−0.662** | −3.23 | 0.438 |
| `g₂ = d` (degrees) | 9020/9020 | −0.391 | −2.87 | 0.153 |
| `g₃ = (d−d̄)f` | 9020/9020 | −0.662 | −3.23 | 0.438 |
| `g₄ = [D,A]f` (commutator) | 9020/9020 | −0.628 | −4.28 | 0.395 |

- **`g₁ ≡ g₃` identically:** `(d−d̄)f = Df − d̄·f`, and projecting onto `f⊥` removes
  the `d̄·f` term — so the "degree-centered × Fiedler" vector *is* the projected `Df`.
- **All correlations are negative.** Larger degree-misalignment energy ⇒ *smaller*
  B2′ slack. The natural perturbations point the **wrong way**; `target ≈ a − b·E`
  (affine `b<0`), never `target = c·E`.
- `g₄ = D(Af) − A(Df) = [D,A]f` (oriented degree gradient) is the most structured
  candidate and still anti-correlates (−0.628).

---

## TASK 3 — exact relation: none

Regressing `target` on the full span of second-variation quadratics in `g₁…g₄`
(the energies `Eᵢ` and cross-terms `Xᵢⱼ = gᵢᵀ(L−λ₂)gⱼ`, which generate any
`(Σcᵢgᵢ)ᵀ(L−λ₂)(Σcᵢgᵢ)`):

> **R² = −1.75**, max residual 11.8, mean |resid| 2.51.

So `C + R″` does **not** lie in the span of these second variations — it is *not*
`gᵀ(L−λ₂)g` for any `g ∈ span{g₁,g₂,g₃,g₄}`, exactly or approximately.

**Caveat on "existence".** Because `target ≥ 0` and `L−λ₂` is PSD on `1⊥` (1-dim
kernel at `f`), `target = gᵀ(L−λ₂)g` *does* hold for some `g` (e.g. along higher
eigenvectors), but **no natural/constructive degree-built `g` realizes it** — the
content is finding such a `g`, and the obvious ones fail.

---

## Synthesis

The hoped-for split — "prove `R″≥0` easily, then certify `C≥−R″` variationally" —
**does not separate the difficulty**:

- `R″ ≥ 0` already requires the *minimality* of `λ₂` (its matrix `N` is indefinite,
  and the property fails for 44% of non-minimal eigenvectors). It is not a free
  linear-algebra lemma but a genuine Fiedler-minimality statement.
- The B2′ slack `C+R″` is **anti-correlated** with every natural second-variation
  energy and lies outside their span, so the straightforward perturbation route is
  closed.

Both observations reinforce the standing conclusion (global-variational round): B (=
B2′) is intrinsically a **minimality** phenomenon — it needs that `f` *minimizes* the
Rayleigh quotient on `1⊥`, used in a way that couples to the indefinite degree
operators. The productive next step is the constrained Courant–Fischer
characterization `λ₂ = inf_{g⊥1} gᵀLg/‖g‖²` applied to a test vector chosen to *lower*-
bound `C+R″` (not the degree-perturbations tried here, which upper-bound the wrong
quantity). This is also the missing Mathlib primitive.

### Caveats
`λ₂`, `f` numerical; all statistics over the 9020 distinct corpus graphs (`n≤9`).
`R″≥0` and `target≥0` verified to `1e-6`; `N`-indefiniteness via `λ_min` on `1⊥`;
the eigenvector test over all 69688 `(graph, i≥2)` pairs. The reduction `B ⟸ B2′`
remains rigorous; B2′ itself is unproven.
