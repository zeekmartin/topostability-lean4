import Topostability.Defs
import Topostability.Shared
import Topostability.Paper14
import Topostability.Paper15
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Conjecture B — proof skeleton

Conjecture B: for a connected graph `G` with the triangle graph `T(G)` connected,
`λ₂(T(G)) ≤ λ₂(G)`.

Via the projected Fiedler lift this reduces to the **triangle-energy lift inequality**
`T ≤ λ₂·(fᵀQf − S²/m)` (`Q = D+A`, `S = Σ d_v f_v`, `m = |E|`, `f` the unit Fiedler).
We prove that inequality by a **regime split** on the sign of
`Required := λ₂(λ₂ + S²/m − fᵀDf)`:

* **Regime (i) `Required ≤ 0`** — closed here, modulo the aggregate triangle-Poincaré
  `T ≤ λ₂·fᵀDf` (`aggregate_triangle_poincare`, open). Algebra: `Required ≤ 0` gives
  `fᵀDf ≥ λ₂ + S²/m`, hence `fᵀQf − S²/m = 2fᵀDf − λ₂ − S²/m ≥ fᵀDf`, so
  `T ≤ λ₂fᵀDf ≤ λ₂(fᵀQf − S²/m)`.
* **Regime (ii) `Required > 0`** — the bottleneck regime (`conjectureB_regime_two`, open;
  empirically `Deficit/Required ≥ 1.7`).

Everything is stated in the **ordered** form `T_ord = Σ_{i,j}[i~j]|N(i)∩N(j)|(f_i−f_j)²`
(`= 2·Σ_{ab∈E} t_ab(f_a−f_b)²`, matching `apex_triangle_energy_identity` in `Paper15`),
so the inequalities carry a factor `2`. Supporting facts in the repo: the apex identity
(`Paper15`), value/gradient hub-flatness (`Paper14`), and `triCount_le_min_degree_sub_one`.
-/

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ordered triangle (Dirichlet) energy
`T_ord = Σ_{i,j} [i~j] · |N(i)∩N(j)| · (f_i − f_j)²`. Equals `2·Σ_{ab∈E} t_ab(f_a−f_b)²`. -/
def triEnergy (f : V → ℝ) : ℝ :=
  ∑ i : V, ∑ j : V,
    if G.Adj i j then ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) * (f i - f j) ^ 2
    else 0

/-- `fᵀDf = Σ_v d_v · f_v²`. -/
def degQuad (f : V → ℝ) : ℝ := ∑ v : V, (G.degree v : ℝ) * (f v) ^ 2

/-- `S = Σ_v d_v · f_v`. -/
def degLin (f : V → ℝ) : ℝ := ∑ v : V, (G.degree v : ℝ) * f v

/-- **Gap energy** `= 2λ(2·fᵀDf − λ − S²/mE) − T = RHS − triEnergy`; the lift bound is `gapEnergy ≥ 0`
(`informal/conjecture_B_aggregate_slack.md`). -/
noncomputable def gapEnergy (f : V → ℝ) (lam mE : ℝ) : ℝ :=
  2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) - triEnergy G f

/-- **Aggregate slack** `S_agg = 2λ·fᵀDf − T` (the slack of `aggregate_triangle_poincare`; `≥ 0`). -/
def aggregateSlack (f : V → ℝ) (lam : ℝ) : ℝ :=
  2 * lam * degQuad G f - triEnergy G f

/-- **`Required`** `= 2λ(λ + S²/mE − fᵀDf) = −E`; `> 0` exactly in regime ii (the hard band `E < 0`),
`≤ 0` in regime i. The aggregate-slack identity reads `gapEnergy = aggregateSlack − required`
(`informal/conjecture_B_hard_band_E_negative.md`). -/
noncomputable def required (f : V → ℝ) (lam mE : ℝ) : ℝ :=
  2 * lam * (lam + (degLin G f) ^ 2 / mE - degQuad G f)

/-- Triangle degree `τ_v = Σ_{u∼v} |N(v)∩N(u)|` (= twice the number of triangles through `v`).
Appears as the diagonal weight in `triEnergy_diag_corr`. -/
def triDeg (v : V) : ℝ := ∑ u : V, if G.Adj v u then (triCount G v u : ℝ) else 0

/-- **Diagonal/correlation identity (algebraic — no spectral hypothesis).**

`triEnergy = 2·Σ_v τ_v f_v² − 2·Σ_{i,j}[i∼j] t_ij f_i f_j`, obtained by expanding the square
`(f_i−f_j)² = f_i²+f_j²−2f_i f_j` and collapsing the two diagonal terms by symmetry of
`t_ij = |N(i)∩N(j)|`. This is the exact decomposition underlying the nodal analysis in
`informal/conjecture_B_nodal_decomposition.md`: the second sum is the triangle correlation
`C`, which splits globally into a same-sign reservoir minus the hard cross mass. -/
lemma triEnergy_diag_corr (f : V → ℝ) :
    triEnergy G f
      = 2 * (∑ i : V, triDeg G i * (f i) ^ 2)
        - 2 * (∑ i : V, ∑ j : V,
            if G.Adj i j then (triCount G i j : ℝ) * (f i * f j) else 0) := by
  simp only [triEnergy, triDeg, triCount]
  set C : V → V → ℝ := fun i j => ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) with hC
  have hCsymm : ∀ a b : V, C a b = C b a := by
    intro a b; simp only [hC]; rw [Finset.inter_comm]
  have hpull : ∀ i : V, (∑ j : V, if G.Adj i j then C i j * (f i) ^ 2 else 0)
      = (∑ j : V, if G.Adj i j then C i j else 0) * (f i) ^ 2 := by
    intro i; rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : G.Adj i j <;> simp [h]
  have hsymm : (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f j) ^ 2 else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i) ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : G.Adj a b
    · have hba : G.Adj b a := h.symm
      rw [if_pos h, if_pos hba, hCsymm b a]
    · have hba : ¬ G.Adj b a := fun x => h x.symm
      rw [if_neg h, if_neg hba]
  have hexp : ∀ i j : V,
      (if G.Adj i j then C i j * (f i - f j) ^ 2 else 0)
      = (if G.Adj i j then C i j * (f i) ^ 2 else 0)
        + (if G.Adj i j then C i j * (f j) ^ 2 else 0)
        - 2 * (if G.Adj i j then C i j * (f i * f j) else 0) := by
    intro i j; by_cases h : G.Adj i j <;> simp [h] <;> ring
  calc (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i - f j) ^ 2 else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i) ^ 2 else 0)
          + (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f j) ^ 2 else 0)
          - 2 * (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i * f j) else 0) := by
        simp_rw [hexp]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (∑ i : V, (∑ j : V, if G.Adj i j then C i j else 0) * (f i) ^ 2)
          - 2 * (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i * f j) else 0) := by
        rw [hsymm, ← Finset.sum_add_distrib]
        simp_rw [hpull, ← two_mul]
        rw [← Finset.mul_sum]

/-- **Diagonal/correlation identity, surplus form.** For any scalar `lam`,
`triEnergy − 2·lam·degQuad = 2·Σ_v (τ_v − lam·d_v) f_v² − 2·Σ_{i,j}[i∼j] t_ij f_i f_j`.
The aggregate triangle-Poincaré `triEnergy ≤ 2·λ₂·degQuad` is therefore equivalent to
`Σ_v(τ_v−λ₂d_v)f_v² ≤ Σ_{i,j}[i∼j] t_ij f_i f_j` (diagonal ≤ triangle correlation). -/
lemma triEnergy_sub_two_lam_degQuad (f : V → ℝ) (lam : ℝ) :
    triEnergy G f - 2 * lam * degQuad G f
      = 2 * (∑ i : V, (triDeg G i - lam * (G.degree i : ℝ)) * (f i) ^ 2)
        - 2 * (∑ i : V, ∑ j : V,
            if G.Adj i j then (triCount G i j : ℝ) * (f i * f j) else 0) := by
  rw [triEnergy_diag_corr, degQuad]
  have step : (∑ i : V, (triDeg G i - lam * (G.degree i : ℝ)) * (f i) ^ 2)
      = (∑ i : V, triDeg G i * (f i) ^ 2) - lam * (∑ v : V, (G.degree v : ℝ) * (f v) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [step]; ring

/-- **Row equation (algebraic).** For any Laplacian eigenpair `(lam, f)` (`L f = lam • f`),
the adjacency satisfies `A f = D f − lam • f` (`A = adjMatrix`, `D = degMatrix`, `L = D − A`). -/
lemma adjMatrix_mulVec_fiedler (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    (G.adjMatrix ℝ).mulVec f = (G.degMatrix ℝ).mulVec f - lam • f := by
  have hLDA : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
  rw [hLDA, Matrix.sub_mulVec] at heig
  rw [← heig]; abel

/-- **Triangle-level row equation (algebraic).** `A² f = A·(D f) − lam·(D f − lam·f)`. Since
`(A²)_{vu} = |N(v)∩N(u)|`, this lifts the row equation to the triangle level — the exact identity
behind the domain-local triangle analysis (`informal/conjecture_B_domain_triangle_perron.md`).
The triangle *energy* uses the Hadamard weight `A∘A²`, not `A²`, so this recursion bridges to
triangles only up to the open 2-path (non-adjacent common-neighbour) terms — see
`informal/conjecture_B_A2_triangle_gap.md`. -/
lemma adjSq_mulVec_fiedler (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    ((G.adjMatrix ℝ) ^ 2).mulVec f
      = (G.adjMatrix ℝ).mulVec ((G.degMatrix ℝ).mulVec f)
        - lam • ((G.degMatrix ℝ).mulVec f - lam • f) := by
  have hA := adjMatrix_mulVec_fiedler G f lam heig
  rw [pow_two, ← Matrix.mulVec_mulVec, hA,
      Matrix.mulVec_sub, Matrix.mulVec_smul, hA]

/-- **Apex sum-of-squares identity (algebraic, symmetry only).** `fᵀA²f = Σ_v ((A f)_v)²`, i.e.
the full 2-path quadratic form is the sum over apices `c` of the squared neighbourhood sums
`(A f)_c = Σ_{a∈N(c)} f_a`. With the eigen-equation `A f = (D−lam)f` this equals
`Σ_v (d_v−lam)² f_v²`, the recursion that controls both the closed (triangle) and open 2-path
energies. No spectral hypothesis is needed for this form. -/
lemma quadForm_adjSq_eq_normSq (f : V → ℝ) :
    dotProduct f (((G.adjMatrix ℝ) ^ 2).mulVec f)
      = ∑ v : V, ((G.adjMatrix ℝ).mulVec f v) ^ 2 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      show (G.adjMatrix ℝ).transpose = G.adjMatrix ℝ from G.transpose_adjMatrix]
  simp only [dotProduct, pow_two]

/-- **Quadratic form of the eigen-equation (algebraic).** `fᵀAf = fᵀDf − lam·(f·f)` for any
Laplacian eigenpair `(lam, f)` (`L f = lam • f`, `A = adjMatrix`, `D = degMatrix`). For a unit
vector this is `fᵀAf = fᵀDf − lam`, the bridge `lam·fᵀAf = lam(fᵀDf − lam)` used to recast the
open-2-path reformulation as `Open + 𝒜 ≥ lam·fᵀAf` (`informal/conjecture_B_hub_correction.md`). -/
lemma quadForm_adjMatrix_fiedler (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    dotProduct f ((G.adjMatrix ℝ).mulVec f)
      = dotProduct f ((G.degMatrix ℝ).mulVec f) - lam * dotProduct f f := by
  rw [adjMatrix_mulVec_fiedler G f lam heig]
  simp only [dotProduct]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Degree-assortativity edge identity (algebraic, symmetry only).** The diagonal
`Σ_v(σ_v − d_v²)f_v²` (`σ_v = Σ_{c∼v}d_c`), written as `Σ_{i,j}[i∼j](d_j−d_i)f_i²`, equals the
edge-antisymmetry `−½·Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)`. This is the negative (high-degree hub)
part of the diagonal `R_v` in the open-2-path reformulation of `aggregate_triangle_poincare`
(`informal/conjecture_B_open2path_gap.md`): the hub negativity is an edge antisymmetry between
degree and `f²`. No spectral hypothesis. -/
lemma degAssort_edge_identity (f : V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then ((G.degree j : ℝ) - G.degree i) * (f i) ^ 2 else 0)
      = - (1 / 2) * ∑ i : V, ∑ j : V,
          (if G.Adj i j then ((G.degree i : ℝ) - G.degree j) * ((f i) ^ 2 - (f j) ^ 2) else 0) := by
  set A1 : V → V → ℝ :=
    fun i j => if G.Adj i j then ((G.degree j : ℝ) - G.degree i) * (f i) ^ 2 else 0 with hA1
  set A2 : V → V → ℝ :=
    fun i j => if G.Adj i j then ((G.degree i : ℝ) - G.degree j) * ((f i) ^ 2 - (f j) ^ 2) else 0
    with hA2
  have hpt : ∀ i j : V, A1 i j + A1 j i = - A2 i j := by
    intro i j; simp only [hA1, hA2]
    by_cases h : G.Adj i j
    · have h' : G.Adj j i := h.symm
      rw [if_pos h, if_pos h', if_pos h]; ring
    · have h' : ¬ G.Adj j i := fun x => h x.symm
      rw [if_neg h, if_neg h', if_neg h]; ring
  have hswap : (∑ i : V, ∑ j : V, A1 i j) = ∑ i : V, ∑ j : V, A1 j i := Finset.sum_comm
  have hsum : (∑ i : V, ∑ j : V, A1 i j) + (∑ i : V, ∑ j : V, A1 j i)
      = ∑ i : V, ∑ j : V, - A2 i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  rw [← hswap] at hsum
  have hneg : (∑ i : V, ∑ j : V, - A2 i j) = - ∑ i : V, ∑ j : V, A2 i j := by
    simp only [Finset.sum_neg_distrib]
  rw [hneg] at hsum
  linarith [hsum]

/-- **Laplacian bilinear (Dirichlet) form (algebraic, no spectral hypothesis).** For any vectors
`u, w`, `uᵀ L w = Σ_{i,j}[i∼j] u_i (w_i − w_j)`. The bilinear extension of the Dirichlet energy;
specialised below at `u = d`, `w = f∘f` to identify the assortativity correction as a covariance. -/
lemma lapMatrix_bilin (u w : V → ℝ) :
    dotProduct u ((G.lapMatrix ℝ).mulVec w)
      = ∑ i : V, ∑ j : V, if G.Adj i j then u i * (w i - w j) else 0 := by
  have hrow : ∀ i : V, ((G.lapMatrix ℝ).mulVec w) i
      = ∑ j : V, if G.Adj i j then (w i - w j) else 0 := by
    intro i
    have hLDA : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
    rw [hLDA, Matrix.sub_mulVec, Pi.sub_apply]
    rw [show (G.degMatrix ℝ).mulVec w i = (G.degree i : ℝ) * w i from by
      simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]]
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [show (∑ j : V, if G.Adj i j then (w i - w j) else 0)
        = ∑ j ∈ G.neighborFinset i, (w i - w j) from by
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]]
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : G.Adj i j <;> simp [h]

/-- **Covariance form of the degree–Fiedler assortativity (algebraic, no spectral hypothesis).**
`𝒜 = dᵀ L (f∘f) = ½ Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)`: the load-bearing hub-correction term in the
open-2-path reformulation of `aggregate_triangle_poincare` is exactly the graph-Laplacian
*covariance* of the degree vector `d` and the squared Fiedler vector `f∘f`
(`informal/conjecture_B_global_summation_parts.md`). It is `≤ 0` whenever degree and `f²` are
anti-monotone across edges (hub-flatness). Specialises `lapMatrix_bilin` at `u = d`, `w = f∘f`. -/
lemma degAssort_covariance (f : V → ℝ) :
    dotProduct (fun v => (G.degree v : ℝ)) ((G.lapMatrix ℝ).mulVec (fun v => (f v) ^ 2))
      = (1 / 2) * ∑ i : V, ∑ j : V,
          (if G.Adj i j then ((G.degree i : ℝ) - G.degree j) * ((f i) ^ 2 - (f j) ^ 2) else 0) := by
  rw [lapMatrix_bilin G]
  set a : V → V → ℝ :=
    fun i j => if G.Adj i j then (G.degree i : ℝ) * ((f i) ^ 2 - (f j) ^ 2) else 0 with ha
  set B : V → V → ℝ :=
    fun i j => if G.Adj i j then ((G.degree i : ℝ) - G.degree j) * ((f i) ^ 2 - (f j) ^ 2) else 0
    with hB
  have hpt : ∀ i j : V, B i j = a i j + a j i := by
    intro i j; simp only [ha, hB]
    by_cases h : G.Adj i j
    · have h' : G.Adj j i := h.symm
      rw [if_pos h, if_pos h, if_pos h']; ring
    · have h' : ¬ G.Adj j i := fun x => h x.symm
      rw [if_neg h, if_neg h, if_neg h']; ring
  have hswap : (∑ i : V, ∑ j : V, a i j) = ∑ i : V, ∑ j : V, a j i := Finset.sum_comm
  have hBsum : (∑ i : V, ∑ j : V, B i j)
      = (∑ i : V, ∑ j : V, a i j) + (∑ i : V, ∑ j : V, a j i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  rw [← hswap] at hBsum
  linarith [hBsum]

/-- **Degree-weighted summation-by-parts identity (spectral).** Multiplying the row equation
`A f = (D−lam) f` by the degree-weighted multiplier `d_v f_v` and summing:
`(D f)ᵀ(A f) = Σ_v d_v (d_v − lam) f_v²`, equivalently `Σ_{ab∈E}(d_a+d_b)f_a f_b
= Σ_v d_v(d_v−lam)f_v²`. The `w = d` member of the edge↔diagonal SBP family
(`informal/conjecture_B_global_summation_parts.md`): it converts a degree-weighted *edge*
correlation into a degree *diagonal*, with the eigenvalue entering linearly. -/
lemma quadForm_deg_adjMatrix_fiedler (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    dotProduct ((G.degMatrix ℝ).mulVec f) ((G.adjMatrix ℝ).mulVec f)
      = ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - lam) * (f v) ^ 2 := by
  have hA := adjMatrix_mulVec_fiedler G f lam heig
  have hDf : (G.degMatrix ℝ).mulVec f = fun v => (G.degree v : ℝ) * f v := by
    funext v; simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]
  rw [hA, hDf]
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- **Neighbourhood variance (Dirichlet) identity (algebraic, no spectral hypothesis).** Over the
neighbours of any apex `c`, the full ordered Dirichlet energy is
`Σ_{a,b∈N(c)}(f_a−f_b)² = 2·d_c·(Σ_{v∈N(c)} f_v²) − 2·(Σ_{v∈N(c)} f_v)²`. The per-apex building
block of the open-2-path / triangle energy split (`informal/conjecture_B_open_apex_pairing.md`):
splitting the pair sum by adjacency gives `Open_c + T_c` on the left, and with the eigen-recursion
`Σ_{v∈N(c)} f_v = (d_c−λ₂)f_c` the right side becomes `2 d_c·mass_c − 2(d_c−λ₂)² f_c²`. -/
lemma neighbor_dirichlet_identity (f : V → ℝ) (c : V) :
    ∑ a ∈ G.neighborFinset c, ∑ b ∈ G.neighborFinset c, (f a - f b) ^ 2
      = 2 * (G.degree c : ℝ) * (∑ v ∈ G.neighborFinset c, (f v) ^ 2)
        - 2 * (∑ v ∈ G.neighborFinset c, f v) ^ 2 := by
  set S := G.neighborFinset c with hS
  have hcard : (S.card : ℝ) = (G.degree c : ℝ) := by
    rw [hS, SimpleGraph.card_neighborFinset_eq_degree]
  have hP1 : (∑ a ∈ S, ∑ _b ∈ S, (f a) ^ 2) = (S.card : ℝ) * ∑ v ∈ S, (f v) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hP2 : (∑ _a ∈ S, ∑ b ∈ S, (f b) ^ 2) = (S.card : ℝ) * ∑ v ∈ S, (f v) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hP3 : (∑ a ∈ S, ∑ b ∈ S, f a * f b) = (∑ v ∈ S, f v) ^ 2 := by
    rw [← Finset.sum_mul_sum, pow_two]
  have hsplit : (∑ a ∈ S, ∑ b ∈ S, (f a - f b) ^ 2)
      = (∑ a ∈ S, ∑ b ∈ S, (f a) ^ 2) + (∑ a ∈ S, ∑ b ∈ S, (f b) ^ 2)
        - 2 * (∑ a ∈ S, ∑ b ∈ S, f a * f b) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsplit, hP1, hP2, hP3, hcard]; ring

/-- **Carré-du-champ product rule for the graph Laplacian (algebraic, no spectral hypothesis).**
`(L(f∘f))_v = 2·f_v·(Lf)_v − Σ_{u∼v}(f_v−f_u)²`, i.e. `L(f²) = 2 f·Lf − 2Γ(f)` with the Bakry–Émery
carré du champ `Γ(f)(v) = ½Σ_{u∼v}(f_v−f_u)²`. At a Laplacian eigenvector (`Lf = λ₂·f`) this is the
eigenfunction Bochner identity `L(f²) = 2λ₂·f² − 2Γ(f)`, which (degree-averaged) recasts the
covariance correction as a carré du champ: `𝒜 = Cov_L(d,f²) = 2λ₂·fᵀDf − 2⟨d,Γ(f)⟩`
(`informal/conjecture_B_bochner_open_paths.md`). -/
lemma lapMatrix_mulVec_sq (f : V → ℝ) (v : V) :
    (G.lapMatrix ℝ).mulVec (fun w => (f w) ^ 2) v
      = 2 * f v * ((G.lapMatrix ℝ).mulVec f v)
        - ∑ u : V, if G.Adj v u then (f v - f u) ^ 2 else 0 := by
  have hrow : ∀ (g : V → ℝ) (x : V), ((G.lapMatrix ℝ).mulVec g) x
      = ∑ u : V, if G.Adj x u then (g x - g u) else 0 := by
    intro g x
    have hLDA : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
    rw [hLDA, Matrix.sub_mulVec, Pi.sub_apply]
    rw [show (G.degMatrix ℝ).mulVec g x = (G.degree x : ℝ) * g x from by
      simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]]
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [show (∑ u : V, if G.Adj x u then (g x - g u) else 0)
        = ∑ u ∈ G.neighborFinset x, (g x - g u) from by
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]]
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul]
  rw [hrow (fun w => (f w) ^ 2) v, hrow f v, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : G.Adj v u
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- **Zero column-sum of the graph Laplacian (algebraic).** `Σ_v (L g)_v = 0` for any `g`
(`L = D − A`; the Dirichlet form `Σ_{i,j}[i∼j](g_i−g_j)` is antisymmetric). This is the engine of
the integrated Bochner identity: with the carré du champ `Γ(f)` (`Σ_v Γ(f)(v) = fᵀLf`) and
`Γ₂(f) = ½·L Γ(f) − λ₂·Γ(f)` (eigenvector), it gives `Σ_v Γ₂(f)(v) = −λ₂·Σ_v Γ(f)(v) = −λ₂²`
(`informal/conjecture_B_weighted_bochner.md`). -/
lemma lapMatrix_mulVec_sum_zero (g : V → ℝ) :
    ∑ v : V, (G.lapMatrix ℝ).mulVec g v = 0 := by
  have hrow : ∀ (x : V), ((G.lapMatrix ℝ).mulVec g) x
      = ∑ u : V, if G.Adj x u then (g x - g u) else 0 := by
    intro x
    have hLDA : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
    rw [hLDA, Matrix.sub_mulVec, Pi.sub_apply]
    rw [show (G.degMatrix ℝ).mulVec g x = (G.degree x : ℝ) * g x from by
      simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]]
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [show (∑ u : V, if G.Adj x u then (g x - g u) else 0)
        = ∑ u ∈ G.neighborFinset x, (g x - g u) from by
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]]
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul]
  simp_rw [hrow]
  set a : V → V → ℝ := fun v u => if G.Adj v u then (g v - g u) else 0 with ha
  have hanti : ∀ v u : V, a u v = - a v u := by
    intro v u; simp only [ha]
    by_cases h : G.Adj v u
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun x => h x.symm)]; ring
  have h1 : (∑ v : V, ∑ u : V, a v u) = ∑ v : V, ∑ u : V, a u v := Finset.sum_comm
  have h2 : (∑ v : V, ∑ u : V, a u v) = - ∑ v : V, ∑ u : V, a v u := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun u _ => hanti v u
  linarith [h1, h2]

/-- **Weighted-Laplacian quadratic form / sum-of-squares (algebraic).** For any *symmetric* weight
matrix `W`, the `W`-Dirichlet energy is `Σ_{i,j} W_ij (f_i−f_j)² = 2[Σ_i (Σ_j W_ij) f_i² −
Σ_{i,j} W_ij f_i f_j]`, i.e. `fᵀ(diag(rowSum W) − W)f = ½ Σ_{i,j} W_ij (f_i−f_j)²`. Specialising
`W = P` (the open-2-path operator `P_ab = #common nbrs with a≁b`) gives the manifest sum-of-squares
`Open = fᵀL_P f = Σ_{a<b} P_ab (f_a−f_b)²`, i.e. `L_P = B_openᵀ B_open` with one row per open
cherry (`informal/conjecture_B_open2path_operator.md`). No spectral hypothesis. -/
lemma quadForm_weighted_laplacian (W : Matrix V V ℝ) (hsymm : ∀ i j : V, W i j = W j i)
    (f : V → ℝ) :
    ∑ i : V, ∑ j : V, W i j * (f i - f j) ^ 2
      = 2 * (∑ i : V, (∑ j : V, W i j) * (f i) ^ 2)
        - 2 * (∑ i : V, ∑ j : V, W i j * (f i * f j)) := by
  have hpull : ∀ i : V, (∑ j : V, W i j * (f i) ^ 2) = (∑ j : V, W i j) * (f i) ^ 2 := by
    intro i; rw [Finset.sum_mul]
  have hsymm2 : (∑ i : V, ∑ j : V, W i j * (f j) ^ 2)
      = ∑ i : V, ∑ j : V, W i j * (f i) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm b a]
  have hexp : ∀ i j : V, W i j * (f i - f j) ^ 2
      = W i j * (f i) ^ 2 + W i j * (f j) ^ 2 - 2 * (W i j * (f i * f j)) := fun i j => by ring
  calc (∑ i : V, ∑ j : V, W i j * (f i - f j) ^ 2)
      = (∑ i : V, ∑ j : V, W i j * (f i) ^ 2) + (∑ i : V, ∑ j : V, W i j * (f j) ^ 2)
          - 2 * (∑ i : V, ∑ j : V, W i j * (f i * f j)) := by
        simp_rw [hexp]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (∑ i : V, (∑ j : V, W i j) * (f i) ^ 2)
          - 2 * (∑ i : V, ∑ j : V, W i j * (f i * f j)) := by
        rw [hsymm2, ← two_mul]
        have hrw : (∑ i : V, ∑ j : V, W i j * (f i) ^ 2)
            = ∑ i : V, (∑ j : V, W i j) * (f i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => hpull i
        rw [hrw]

/-- **Adjacency column-sum / weighted handshake (algebraic).** `Σ_v (A f)_v = Σ_v d_v f_v`, i.e.
`1ᵀ A f = S` (`S = Σ_v d_v f_v`). With `1ᵀ D f = S` this gives `1ᵀ(D+A)f = 2S` — the off-diagonal
`⟨u₁, (λ₂Q − L_M) u₂⟩ = λ₂·2S/√n` of the 2×2 low-frequency `{const, Fiedler}` block of
`M = λ₂Q − L_M`, whose positive-semidefiniteness is exactly Conjecture B; the `S²` it contributes is
the `S²/m` correction of the lift bound (`informal/conjecture_B_spectral_orthogonality.md`).
No spectral hypothesis. -/
lemma adjMatrix_mulVec_sum (f : V → ℝ) :
    ∑ v : V, (G.adjMatrix ℝ).mulVec f v = ∑ u : V, (G.degree u : ℝ) * f u := by
  have hrow : ∀ v : V, (G.adjMatrix ℝ).mulVec f v
      = ∑ u : V, if G.Adj v u then f u else 0 := by
    intro v
    rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hfac : (∑ v : V, if G.Adj v u then f u else 0)
      = (∑ v : V, if G.Adj v u then (1 : ℝ) else 0) * f u := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : G.Adj v u <;> simp [h]
  rw [hfac]
  have hcnt : (∑ v : V, if G.Adj v u then (1 : ℝ) else 0) = (G.degree u : ℝ) := by
    rw [Finset.sum_boole]
    rw [show (Finset.univ.filter (fun v => G.Adj v u)) = G.neighborFinset u from by
      ext v; simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]]
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  rw [hcnt]

/-- **Lagrange identity (Gram determinant = sum of squares).** For any `a, b : ι → ℝ`,
`(Σ aᵢ²)(Σ bᵢ²) − (Σ aᵢbᵢ)² = ½ Σ_{i,j}(aᵢbⱼ − aⱼbᵢ)²` — the Cauchy–Schwarz/Gram-determinant gap as
a manifest sum of squares. Specialising `a = h` (edge-lift `hₑ = f_a+f_b`), `b = 1` gives the
manifestly-nonnegative part of the determinant `det(M_low) = (4λ₂/n)(λ₂·G − m·T)`, namely
`G = m·fᵀQf − S² = ½ Σ_{e,e'}(hₑ − h_{e'})² = m²·Var_E(h) ≥ 0`
(`informal/conjecture_B_determinant_form.md`). -/
lemma lagrange_identity {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i : ι, (a i) ^ 2) * (∑ i : ι, (b i) ^ 2) - (∑ i : ι, a i * b i) ^ 2
      = (1 / 2) * ∑ i : ι, ∑ j : ι, (a i * b j - a j * b i) ^ 2 := by
  have hAA : (∑ i : ι, ∑ j : ι, (a i) ^ 2 * (b j) ^ 2)
      = (∑ i : ι, (a i) ^ 2) * (∑ j : ι, (b j) ^ 2) := by
    rw [← Finset.sum_mul_sum]
  have hBB : (∑ i : ι, ∑ j : ι, (a j) ^ 2 * (b i) ^ 2)
      = (∑ i : ι, (a i) ^ 2) * (∑ j : ι, (b j) ^ 2) := by
    rw [Finset.sum_comm, ← Finset.sum_mul_sum]
  have hAB : (∑ i : ι, ∑ j : ι, 2 * ((a i * b i) * (a j * b j)))
      = 2 * ((∑ i : ι, a i * b i) * (∑ j : ι, a j * b j)) := by
    have h2 : (∑ i : ι, ∑ j : ι, 2 * ((a i * b i) * (a j * b j)))
        = 2 * ∑ i : ι, ∑ j : ι, (a i * b i) * (a j * b j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    rw [h2, ← Finset.sum_mul_sum]
  have hsplit : (∑ i : ι, ∑ j : ι, (a i * b j - a j * b i) ^ 2)
      = (∑ i : ι, ∑ j : ι, (a i) ^ 2 * (b j) ^ 2)
        + (∑ i : ι, ∑ j : ι, (a j) ^ 2 * (b i) ^ 2)
        - (∑ i : ι, ∑ j : ι, 2 * ((a i * b i) * (a j * b j))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hAA, hBB, hAB]; ring

/-- **Variance identity (sum-of-squares form).** `(Σ xᵢ²)·N − (Σ xᵢ)² = ½ Σ_{i,j}(xᵢ − xⱼ)²`
(`N = card ι`): `N·Var(x)` as a manifest sum of squares. Corollary of `lagrange_identity` at
`b ≡ 1`. Specialising `x = h` (edge-lift `hₑ = f_a+f_b`, `ι = edges`, `N = m`) gives the
manifestly-nonnegative determinant part `G_det = m·Σhₑ² − S² = ½ Σ_{e,e'}(hₑ − h_{e'})²`, hence
`G = Σhₑ² − S²/m = m·Var_E(h) ≥ 0` in `det(M_low) = (4λ₂/n)(λ₂·G − m·T)`
(`informal/conjecture_B_edge_variance.md`, where B ⟺ `T ≤ λ₂·G`). -/
lemma sum_sq_mul_card_sub_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (∑ i : ι, (x i) ^ 2) * (Fintype.card ι : ℝ) - (∑ i : ι, x i) ^ 2
      = (1 / 2) * ∑ i : ι, ∑ j : ι, (x i - x j) ^ 2 := by
  have h := lagrange_identity x (fun _ => (1 : ℝ))
  simpa using h

/-- **Min-weight decomposition of the B2′ edge energy (algebraic, no spectral hypothesis).** Using
`min(a,b) = (a+b)/2 − |a−b|/2`, the degree-min-weighted gradient energy `B2′ = Σ_e(min(d_a,d_b)−1)g²`
splits into the degree-*average* Dirichlet energy minus the degree-*discrepancy* gradient energy minus
the plain Dirichlet energy. This is the exact edge-variance form of B2′
(`informal/conjecture_B_B2prime_proof.md`): combined with the eigen-equation it gives the slack
decomposition `λ₂G − B2′ = R″ + C` (`R″ = λ₂(fᵀDf−λ₂+1−S²/m)`,
`C = Σ_{edges, h higher-deg}(d_h−d_l)f_h(f_h−f_l)`), with the discrepancy term vanishing on regular
graphs (the equality base case `aggregate_triangle_poincare_regular`). -/
lemma B2prime_min_decomp (f : V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then
        (min (G.degree i : ℝ) (G.degree j) - 1) * (f i - f j) ^ 2 else 0)
      = (1 / 2) * (∑ i : V, ∑ j : V, if G.Adj i j then
            ((G.degree i : ℝ) + G.degree j) * (f i - f j) ^ 2 else 0)
        - (1 / 2) * (∑ i : V, ∑ j : V, if G.Adj i j then
            |(G.degree i : ℝ) - G.degree j| * (f i - f j) ^ 2 else 0)
        - (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) := by
  have hmin : ∀ a b : ℝ, min a b = (a + b) / 2 - |a - b| / 2 := by
    intro a b
    rcases le_total a b with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : G.Adj i j
  · simp only [if_pos h]; rw [hmin]; ring
  · simp only [if_neg h]; ring

/-- **Per-edge triangle bound (algebraic).** For an edge `i∼j`, the number of common neighbours
`triCount = |N(i)∩N(j)|` is at most `min(d_i,d_j) − 1` (a common neighbour avoids both endpoints, so
`N(i)∩N(j) ⊆ N(i).erase j` and `⊆ N(j).erase i`). This is the first step of every regime chain:
it gives `T ≤ B2′` (`T = Σ_e t_e g_e²`, `B2′ = Σ_e(min(d_a,d_b)−1)g_e²`), the reduction of the
triangle inequality to the triangle-free degree-only one
(`informal/conjecture_B_three_regimes_chain.md`). -/
lemma triCount_le_min_degree_sub_one {i j : V} (hij : G.Adj i j) :
    triCount G i j ≤ min (G.degree i) (G.degree j) - 1 := by
  have hle : ∀ a b : V, G.Adj a b →
      (G.neighborFinset a ∩ G.neighborFinset b).card ≤ G.degree a - 1 := by
    intro a b hab
    have hbmem : b ∈ G.neighborFinset a := by rw [SimpleGraph.mem_neighborFinset]; exact hab
    have hsub : G.neighborFinset a ∩ G.neighborFinset b ⊆ (G.neighborFinset a).erase b := by
      intro x hx
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨fun hxj => (G.ne_of_adj (hxj ▸ hx.2)) rfl, hx.1⟩
    calc (G.neighborFinset a ∩ G.neighborFinset b).card
        ≤ ((G.neighborFinset a).erase b).card := Finset.card_le_card hsub
      _ = (G.neighborFinset a).card - 1 := Finset.card_erase_of_mem hbmem
      _ = G.degree a - 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
  have h1 := hle i j hij
  have h2 := hle j i hij.symm
  rw [Finset.inter_comm] at h2
  simp only [triCount]
  omega

/-- Row form of the Laplacian action (generic graph): `(L_H g)_x = Σ_u [x∼u](g_x − g_u)`. -/
lemma lapMatrix_mulVec_row (H : SimpleGraph V) [DecidableRel H.Adj] (g : V → ℝ) (x : V) :
    (H.lapMatrix ℝ).mulVec g x = ∑ u : V, if H.Adj x u then (g x - g u) else 0 := by
  have hLDA : H.lapMatrix ℝ = H.degMatrix ℝ - H.adjMatrix ℝ := rfl
  rw [hLDA, Matrix.sub_mulVec, Pi.sub_apply]
  rw [show (H.degMatrix ℝ).mulVec g x = (H.degree x : ℝ) * g x from by
    simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]]
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  rw [show (∑ u : V, if H.Adj x u then (g x - g u) else 0)
      = ∑ u ∈ H.neighborFinset x, (g x - g u) from by
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]]
  rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]

/-- **Eigenpair invariance under equal-value edge deletion.** If `f` is a Laplacian eigenvector
of `G` with eigenvalue `lam`, `f i = f j`, and `G'` is `G` with the single edge `{i,j}` removed
(its adjacency is `G.Adj a b ∧ s(a,b) ≠ s(i,j)`), then `f` is *still* an eigenvector of `G'` with
the **same** eigenvalue: `L_{G'} f = lam • f`. (Each row of `L f` is unchanged — deleting the edge
`{i,j}` drops, at `i`, the degree term `−f i` and the neighbour term `+f j`, which cancel since
`f i = f j`; symmetrically at `j`; all other rows are untouched.) This is the exact-invariance
fact underlying the TYPE A bulk-rigidity step: deleting interior bulk edges between equal-Fiedler
vertices leaves the Fiedler pair fixed (`informal/conjecture_B_typeA_delta_rigor.md`). -/
theorem eigenpair_invariance_equal_values (G' : SimpleGraph V) [DecidableRel G'.Adj]
    (f : V → ℝ) (lam : ℝ) (i j : V)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hfij : f i = f j)
    (hdiff : ∀ a b : V, G'.Adj a b ↔ (G.Adj a b ∧ ¬ (s(a, b) = s(i, j)))) :
    (G'.lapMatrix ℝ).mulVec f = lam • f := by
  have hpt : ∀ x : V, (G'.lapMatrix ℝ).mulVec f x = (G.lapMatrix ℝ).mulVec f x := by
    intro x
    rw [lapMatrix_mulVec_row G' f x, lapMatrix_mulVec_row G f x]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hG : G.Adj x u
    · by_cases hs : s(x, u) = s(i, j)
      · have hG' : ¬ G'.Adj x u := by rw [hdiff]; tauto
        rw [if_neg hG', if_pos hG]
        rcases Sym2.eq_iff.mp hs with ⟨hx, hu⟩ | ⟨hx, hu⟩
        · rw [hx, hu, hfij]; ring
        · rw [hx, hu, hfij]; ring
      · have hG' : G'.Adj x u := by rw [hdiff]; exact ⟨hG, hs⟩
        rw [if_pos hG', if_pos hG]
    · have hG' : ¬ G'.Adj x u := by rw [hdiff]; tauto
      rw [if_neg hG', if_neg hG]
  funext x
  rw [hpt x, heig]

/-- **TYPE B structural reduction: `T = T_block ≤ W · D_block`.**
For the path-bottleneck regime (`informal/conjecture_B_typeB_path_bottleneck.md`): the triangle
energy `T = triEnergy` is supported entirely on the dense block `B`, because the path/stub and the
boundary edges are *triangle-free* (`hoff`: edges not fully inside `B` carry no common neighbours,
`|N(i)∩N(j)| = 0`). Within `B` the triangle weight is bounded by `W` (`hwt`). Hence
`T ≤ W · D_block`, where `D_block = Σ_{i,j∈B, i∼j}(f_i−f_j)²` is the within-block Dirichlet
(double-sum) energy — the same object split out by `Paper16.quadform_edge_split`. Term-by-term. -/
lemma triEnergy_le_block_dirichlet (f : V → ℝ) (B : Finset V) (W : ℝ)
    (hoff : ∀ i j, G.Adj i j → ¬ (i ∈ B ∧ j ∈ B) →
        (G.neighborFinset i ∩ G.neighborFinset j).card = 0)
    (hwt : ∀ i j, G.Adj i j → i ∈ B → j ∈ B →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ W) :
    triEnergy G f
      ≤ W * (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then (f i - f j) ^ 2 else 0) := by
  rw [triEnergy, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hadj : G.Adj i j
  · by_cases hB : i ∈ B ∧ j ∈ B
    · rw [if_pos hadj, if_pos (show G.Adj i j ∧ i ∈ B ∧ j ∈ B from ⟨hadj, hB.1, hB.2⟩)]
      exact mul_le_mul_of_nonneg_right (hwt i j hadj hB.1 hB.2) (sq_nonneg _)
    · rw [if_pos hadj, hoff i j hadj hB, if_neg (fun h => hB ⟨h.2.1, h.2.2⟩)]
      simp
  · rw [if_neg hadj, if_neg (fun h => hadj h.1)]
    simp

/-- **TYPE B closure (theorem-shaped): `T ≤ (W·Cflat)·λ₂²`.**
Combining the structural reduction with block flatness. Hypotheses encode the TYPE B structure of
`informal/conjecture_B_typeB_path_bottleneck.md`:
* `hoff`/`hwt` — `T` lives on the block with per-edge triangle weight `≤ W` (triangle-free path
  and boundary);
* `hflat` — **block flatness** `D_block ≤ Cflat·λ₂²`, the output of `Paper16.poincare_on_block`
  applied to the induced subgraph `G[B]` (spectral gap `γ`): the resolvent bound forces the
  within-block Dirichlet energy to `O(λ₂²/γ)` (the rigid-block mechanism — the junction flux is
  `O(λ₂)` since the heavy high-gap block cannot follow the path).

Conclusion: **`T ≤ (W·Cflat)·λ₂²`**, i.e. `T = O(λ₂²)`. With `RHS = Θ(λ₂)` (the path edge-lift
variance, bounded below) this gives `T ≤ RHS` for `λ₂` small — Conjecture B on the TYPE B regime. -/
theorem typeB_triEnergy_bound (f : V → ℝ) (B : Finset V) (W Cflat lam2 : ℝ)
    (hW : 0 ≤ W)
    (hoff : ∀ i j, G.Adj i j → ¬ (i ∈ B ∧ j ∈ B) →
        (G.neighborFinset i ∩ G.neighborFinset j).card = 0)
    (hwt : ∀ i j, G.Adj i j → i ∈ B → j ∈ B →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ W)
    (hflat : (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then (f i - f j) ^ 2 else 0)
        ≤ Cflat * lam2 ^ 2) :
    triEnergy G f ≤ (W * Cflat) * lam2 ^ 2 := by
  have h1 := triEnergy_le_block_dirichlet G f B W hoff hwt
  have h2 : W * (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then (f i - f j) ^ 2 else 0)
      ≤ W * (Cflat * lam2 ^ 2) := mul_le_mul_of_nonneg_left hflat hW
  calc triEnergy G f ≤ _ := h1
    _ ≤ W * (Cflat * lam2 ^ 2) := h2
    _ = (W * Cflat) * lam2 ^ 2 := by ring

-- `aggregate_triangle_poincare` (`T ≤ 2λ·degQuad`, regime i) is defined AFTER `triEnergy_le_B2prime`.
-- It is a direct `sorry`: the `B2′` route was REVERTED — `B2′ ≤ 2λ·degQuad` is FALSE on sparse-core
-- deg2+dense (`triEnergy_le_B2prime` is too lossy when there are few triangles, `T ≪ B2′`); see
-- `informal/conjecture_B_signed_cancellation.md`. The regular case is `aggregate_triangle_poincare_regular`.

/-- **Aggregate triangle-Poincaré for regular graphs (no `sorry`).** For a `d`-regular graph and any
Laplacian eigenpair `(lam, f)`, `triEnergy ≤ 2·lam·degQuad` — the regular case of
`aggregate_triangle_poincare`. Proof: each `t_e = |N(a)∩N(b)| ≤ d−1` (a common neighbour avoids the
two edge endpoints), so `T ≤ (d−1)·D` with `D = Σ_{i,j}[i∼j](f_i−f_j)² = 2·lam·‖f‖²` (the Dirichlet
form at the eigenvector); and `2·lam·degQuad = 2·lam·d·‖f‖² = d·D ≥ (d−1)·D` since `D ≥ 0`. No
spectral bound `λ₂ ≤ d+1` is needed — regularity (`degQuad = d‖f‖²`) supplies the factor directly
(`informal/conjecture_B_edge_variance.md`). -/
theorem aggregate_triangle_poincare_regular (f : V → ℝ) (lam : ℝ) (d : ℕ)
    (hreg : ∀ v : V, G.degree v = d)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    triEnergy G f ≤ 2 * lam * degQuad G f := by
  set Sf : ℝ := ∑ v : V, (f v) ^ 2 with hSf
  have hquad : (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) = 2 * lam * Sf := by
    have h1 : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f
        = ∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f) v := by
      rw [Matrix.toLinearMap₂'_apply']; rfl
    have h2 : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f
        = (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) / 2 := by
      rw [SimpleGraph.lapMatrix_toLinearMap₂']
    have h3 : (∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f) v) = lam * Sf := by
      rw [heig, hSf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [h1, h3] at h2
    linarith [h2]
  have hdq : degQuad G f = (d : ℝ) * Sf := by
    rw [degQuad, hSf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hreg v]
  have hcard : ∀ i j : V, G.Adj i j →
      ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ (d : ℝ) - 1 := by
    intro i j hadj
    have hjmem : j ∈ G.neighborFinset i := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
    have hsub : G.neighborFinset i ∩ G.neighborFinset j ⊆ (G.neighborFinset i).erase j := by
      intro x hx
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨fun hxj => (G.ne_of_adj (hxj ▸ hx.2)) rfl, hx.1⟩
    have hcle : (G.neighborFinset i ∩ G.neighborFinset j).card ≤ (G.neighborFinset i).card - 1 := by
      calc (G.neighborFinset i ∩ G.neighborFinset j).card
          ≤ ((G.neighborFinset i).erase j).card := Finset.card_le_card hsub
        _ = (G.neighborFinset i).card - 1 := Finset.card_erase_of_mem hjmem
    have hdeg : (G.neighborFinset i).card = d := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg i
    rw [hdeg] at hcle
    have hd1 : 1 ≤ d := by rw [← hdeg]; exact Finset.card_pos.mpr ⟨j, hjmem⟩
    have hcast : ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcle
    rwa [Nat.cast_sub hd1, Nat.cast_one] at hcast
  have hTle : triEnergy G f
      ≤ ((d : ℝ) - 1) * (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) := by
    rw [triEnergy, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (hcard i j h) (sq_nonneg _)
    · simp
  have hDnn : 0 ≤ (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  calc triEnergy G f
      ≤ ((d : ℝ) - 1) * (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) := hTle
    _ ≤ (d : ℝ) * (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) := by
        nlinarith [hDnn]
    _ = (d : ℝ) * (2 * lam * Sf) := by rw [hquad]
    _ = 2 * lam * degQuad G f := by rw [hdq]; ring

/-- **Regular case of the lift inequality `T ≤ λ₂G` (sorry-free, modulo `λ ≤ d+1`).**
For a connected `d`-regular graph with unit Fiedler `f` (`‖f‖²=1`, `f ⊥ 1`), the *full* triangle-lift
inequality holds: `triEnergy ≤ 2λ(2·degQuad − λ − degLin²/mE)`. Proof
(`informal/conjecture_B_regular_PROOF.md`): `degQuad = d`, `degLin = 0` (regular + `f⊥1`); the per-edge
bound `t_e ≤ d−1` gives `T ≤ (d−1)·(Dirichlet) = (d−1)·2λ`; and `(d−1)·2λ ≤ 2λ(2d−λ)` since `λ ≤ d+1`.
The hypothesis `hlam : λ ≤ d+1` is the standard spectral bound (`μ₂(A) ≥ −1` by Cauchy interlacing on a
`2×2` edge block `[[0,1],[1,0]]` with eigenvalues `±1`); it is left explicit here. This **strictly
strengthens** `aggregate_triangle_poincare_regular` (`T ≤ 2λ·degQuad = 2λd`), which is insufficient in
the dense regime `λ ∈ (d, d+1]` (`K_n`: `λ = d+1`). -/
theorem triEnergy_le_RHS_regular (f : V → ℝ) (lam mE : ℝ) (d : ℕ)
    (hreg : ∀ v : V, G.degree v = d)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hnorm : ∑ v : V, (f v) ^ 2 = 1)
    (hperp : ∑ v : V, f v = 0)
    (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ (d : ℝ) + 1) :
    triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := by
  have hquad : (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) = 2 * lam := by
    have h1 : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f
        = ∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f) v := by
      rw [Matrix.toLinearMap₂'_apply']; rfl
    have h2 : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f
        = (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) / 2 := by
      rw [SimpleGraph.lapMatrix_toLinearMap₂']
    have h3 : (∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f) v) = lam := by
      rw [heig]
      have hh : (∑ v : V, f v * (lam • f) v) = lam * ∑ v : V, (f v) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [hh, hnorm, mul_one]
    rw [h1, h3] at h2
    linarith [h2]
  have hdq : degQuad G f = (d : ℝ) := by
    rw [degQuad]
    have hc : (∑ v : V, (G.degree v : ℝ) * (f v) ^ 2) = ∑ v : V, (d : ℝ) * (f v) ^ 2 := by
      refine Finset.sum_congr rfl fun v _ => ?_; rw [hreg v]
    rw [hc, ← Finset.mul_sum, hnorm, mul_one]
  have hdl : degLin G f = 0 := by
    rw [degLin]
    have hc : (∑ v : V, (G.degree v : ℝ) * f v) = ∑ v : V, (d : ℝ) * f v := by
      refine Finset.sum_congr rfl fun v _ => ?_; rw [hreg v]
    rw [hc, ← Finset.mul_sum, hperp, mul_zero]
  have hcard : ∀ i j : V, G.Adj i j →
      ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ (d : ℝ) - 1 := by
    intro i j hadj
    have hjmem : j ∈ G.neighborFinset i := by rw [SimpleGraph.mem_neighborFinset]; exact hadj
    have hsub : G.neighborFinset i ∩ G.neighborFinset j ⊆ (G.neighborFinset i).erase j := by
      intro x hx
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hx
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨fun hxj => (G.ne_of_adj (hxj ▸ hx.2)) rfl, hx.1⟩
    have hcle : (G.neighborFinset i ∩ G.neighborFinset j).card ≤ (G.neighborFinset i).card - 1 := by
      calc (G.neighborFinset i ∩ G.neighborFinset j).card
          ≤ ((G.neighborFinset i).erase j).card := Finset.card_le_card hsub
        _ = (G.neighborFinset i).card - 1 := Finset.card_erase_of_mem hjmem
    have hdeg : (G.neighborFinset i).card = d := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hreg i
    rw [hdeg] at hcle
    have hd1 : 1 ≤ d := by rw [← hdeg]; exact Finset.card_pos.mpr ⟨j, hjmem⟩
    have hcast : ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcle
    rwa [Nat.cast_sub hd1, Nat.cast_one] at hcast
  have hTle : triEnergy G f
      ≤ ((d : ℝ) - 1) * (∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0) := by
    rw [triEnergy, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (hcard i j h) (sq_nonneg _)
    · simp
  have hT : triEnergy G f ≤ ((d : ℝ) - 1) * (2 * lam) := by rw [← hquad]; exact hTle
  rw [hdq, hdl]
  have h0 : ((0 : ℝ)) ^ 2 / mE = 0 := by norm_num
  rw [h0]
  have hprod : 0 ≤ lam * ((d : ℝ) + 1 - lam) := mul_nonneg hlam0 (by linarith)
  nlinarith [hT, hprod]

/-- **Regime (ii), TYPE B branch (sorry-free).** The path-bottleneck sub-regime of `Required > 0`.
For a graph with a triangle-rich block `B` and a triangle-free path/stub (so the off-block triangle
weights vanish, `hoff`, and the in-block weight is `≤ W`, `hwt`) and block flatness `hflat`
(`D_block ≤ Cflat·λ²`, the `Paper16.poincare_on_block` output), the triangle energy obeys
`T ≤ (W·Cflat)·λ²` (`typeB_triEnergy_bound`); the closing hypothesis `hclose` is the `T-bound ≤ RHS`
inequality (`(W·Cflat)λ² ≤ RHS`, encoding `RHS = Θ(λ) ≥ O(λ²)` for the bottleneck `λ`). Chaining the
two gives the regime-(ii) conclusion. This formally connects the TYPE B branch of regime (ii) to the
proved block lemmas; the general `conjectureB_regime_two` (TYPE A ∪ TYPE B, no structural hypotheses)
remains open — its obstruction is the TYPE A extremality bound `gap/eff ≥ 1/3`
(`informal/CONJECTURE_B_STATUS.md` §10). -/
theorem conjectureB_regime_two_typeB (f : V → ℝ) (B : Finset V) (W Cflat lam mE : ℝ)
    (hW : 0 ≤ W)
    (hoff : ∀ i j, G.Adj i j → ¬ (i ∈ B ∧ j ∈ B) →
        (G.neighborFinset i ∩ G.neighborFinset j).card = 0)
    (hwt : ∀ i j, G.Adj i j → i ∈ B → j ∈ B →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ W)
    (hflat : (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then (f i - f j) ^ 2 else 0)
        ≤ Cflat * lam ^ 2)
    (hclose : (W * Cflat) * lam ^ 2 ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE)) :
    triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) :=
  le_trans (typeB_triEnergy_bound G f B W Cflat lam hW hoff hwt hflat) hclose

/-- **`T ≤ B2′` (sorry-free, independent).** Summing the per-edge triangle bound
`triCount ≤ min(d_a,d_b)−1` (`triCount_le_min_degree_sub_one`): the triangle energy is bounded by
the triangle-free degree energy `B2′ = Σ_{i,j}[i∼j](min(d_i,d_j)−1)(f_i−f_j)²` (ordered double sum).
The `B2′` relaxation is *off* the main `conjectureB_lift` chain (which now uses the direct
`triEnergy_le_RHS`), because `B2′ ≤ λ₂G` is artificially hard on the deg2+dense bottleneck; this lemma
is kept as the standalone relaxation `T ≤ B2′` (`informal/conjecture_B_true_T_vs_B2prime.md`). -/
lemma triEnergy_le_B2prime (f : V → ℝ) :
    triEnergy G f
      ≤ ∑ i : V, ∑ j : V,
          if G.Adj i j then ((min (G.degree i) (G.degree j) - 1 : ℕ) : ℝ) * (f i - f j) ^ 2
          else 0 := by
  rw [triEnergy]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : G.Adj i j
  · rw [if_pos h, if_pos h]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hc : ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) = (triCount G i j : ℝ) := rfl
    rw [hc]
    exact_mod_cast triCount_le_min_degree_sub_one G h
  · rw [if_neg h, if_neg h]

/-- **Aggregate triangle-Poincaré `T ≤ 2λ·degQuad` (regime i, OPEN).** `triEnergy ≤ 2λ·fᵀDf` at any
Laplacian eigenpair. Holds on every tested graph including degenerate eigenspaces (`T/(2λ·degQuad) ≤
0.17` even on sparse-core deg2+dense); the regular case is `aggregate_triangle_poincare_regular`.

**NB — the `B2′` route does NOT prove this** (`informal/conjecture_B_signed_cancellation.md`): the
intermediate `B2′ = Σ_e(min(d_a,d_b)−1)g²` satisfies `triEnergy ≤ B2′` (`triEnergy_le_B2prime`), but
`B2′ ≤ 2λ·degQuad` is **FALSE** on sparse-core deg2+dense (`q ≤ 0.12`, e.g. `deg2d140_0.05`:
`B2′/(2λ·degQuad) = 1.05`, while `triEnergy/(2λ·degQuad) = 0.01`). The per-edge bound `t_e ≤ min−1` is
far too lossy when the core is sparse (few triangles, `T ≪ B2′`), so `B2′` overshoots. The equivalent
`C = ½(A+I) ≥ −λ` form also fails as a general quadratic inequality (the matrix `M_C + L` is indefinite,
min eigenvalue `−0.13`); the eigenvector equation is essential. This lemma must be proved directly. -/
lemma aggregate_triangle_poincare (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    triEnergy G f ≤ 2 * lam * degQuad G f := by
  sorry

/-! ### Regime architecture: `gapEnergy = aggregateSlack − required`

The lift bound `gapEnergy ≥ 0` splits on the sign of `required` (`= −E`,
`informal/conjecture_B_hard_band_E_negative.md`):
* **regime i** (`required ≤ 0`, `E ≥ 0`): the aggregate Poincaré slack alone gives `gap ≥ 0`;
* **regime ii** (`required > 0`, `E < 0`) splits further into the *regular* case (proved via
  `triEnergy_le_RHS_regular`, interlacing `λ ≤ d+1`) and the *TYPE A* case
  (`typeA_extremality_gap_nonneg`, the only intended TYPE A `sorry`).
This recovers the original 3-regime classification with the regime-i case a one-line consequence of the
aggregate Poincaré. -/

/-- **The regime identity** `gapEnergy = aggregateSlack − required` (pure algebra). -/
lemma gap_eq_aggregateSlack_sub_required (f : V → ℝ) (lam mE : ℝ) :
    gapEnergy G f lam mE = aggregateSlack G f lam - required G f lam mE := by
  simp only [gapEnergy, aggregateSlack, required]; ring

/-- **Regime i** (`required ≤ 0`): the aggregate Poincaré slack `aggregateSlack ≥ 0` already gives
`gapEnergy ≥ 0`, since `gapEnergy = aggregateSlack − required`. -/
lemma regime_i_from_aggregate (f : V → ℝ) (lam mE : ℝ)
    (haggr : 0 ≤ aggregateSlack G f lam) (hReq : required G f lam mE ≤ 0) :
    0 ≤ gapEnergy G f lam mE := by
  rw [gap_eq_aggregateSlack_sub_required]; linarith

/-- **Regime ii, regular** (no `sorry`): for a `d`-regular graph the bound holds for *every*
eigenvector (`triEnergy_le_RHS_regular`), hence `gapEnergy ≥ 0`. -/
lemma regime_ii_regular_gap_nonneg (f : V → ℝ) (lam mE : ℝ) (d : ℕ)
    (hreg : ∀ v : V, G.degree v = d)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hnorm : ∑ v : V, (f v) ^ 2 = 1) (hperp : ∑ v : V, f v = 0)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ (d : ℝ) + 1) :
    0 ≤ gapEnergy G f lam mE := by
  have h := triEnergy_le_RHS_regular G f lam mE d hreg heig hnorm hperp hlam0 hlam
  simp only [gapEnergy]; linarith

/-- **Regime ii, TYPE A — the only intended TYPE A `sorry`.** For a connected-triangle-graph host
(`hTconn`) and a Fiedler `f` in the hard band (`required > 0`, i.e. `E < 0`, the low-degree-vertex
bottleneck families: deg2+dense, twin-port), `gapEnergy ≥ 0`. This is the TYPE A extremality content
(`gap/eff ≥ 1/3`, `informal/conjecture_B_hard_band_E_negative.md`); the hypotheses are sound — verified
that `hTconn ⇒ gapEnergy(f) ≥ 0` for every eigenvector (no degenerate counterexample). -/
theorem typeA_extremality_gap_nonneg (f : V → ℝ) (lam mE : ℝ)
    (hTconn : (triangleGraph G).Connected)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hReq : 0 < required G f lam mE) :
    0 ≤ gapEnergy G f lam mE := by
  sorry

/-- **Master regime dispatch.** Given the aggregate Poincaré slack (`aggregateSlack ≥ 0`) and a
connected triangle graph, `gapEnergy ≥ 0`: regime i (`required ≤ 0`) via `regime_i_from_aggregate`,
regime ii (`required > 0`) via `typeA_extremality_gap_nonneg`. -/
theorem gapEnergy_nonneg (f : V → ℝ) (lam mE : ℝ)
    (hTconn : (triangleGraph G).Connected)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (haggr : 0 ≤ aggregateSlack G f lam) :
    0 ≤ gapEnergy G f lam mE := by
  by_cases hR : required G f lam mE ≤ 0
  · exact regime_i_from_aggregate G f lam mE haggr hR
  · exact typeA_extremality_gap_nonneg G f lam mE hTconn heig (not_le.mp hR)

/-- **The lift inequality `T ≤ λ₂G` — EXISTENTIAL form (the universal form is FALSE).**
The *universal* statement `∀ f, L_G f = λf → triEnergy G f ≤ 2λ(2fᵀDf − λ − S²/m)` is **FALSE** when
`λ₂` is degenerate (multiplicity > 1): on `K_d` + pendants (star+clique) a *badly-chosen* Fiedler in the
high-multiplicity `λ₂`-eigenspace gives `triEnergy > λ₂G` (`informal/conjecture_B_AB_minus_D.md`,
`K₁₂+15`: gap `−1.06`). What Conjecture B actually needs (via the projected Fiedler lift, which it may
*choose* from the eigenspace) is the **existential**: among unit Fiedler vectors for `λ`, SOME satisfies
the bound. Verified on all tested graphs: `max gap ≥ 0` over the `λ₂`-eigenspace (a good Fiedler always
exists). The hypotheses provide a witness unit Fiedler `f₀` (the eigenspace is nonempty). NB: the
*regular* case is special — `triEnergy_le_RHS_regular` proves the bound for *every* eigenvector (the
universal form holds there, `gap ≥ λ(d+1−λ) ≥ 0`); degeneracy only breaks the universal form for
*irregular* graphs.

**`hTconn` (triangleGraph connected) is essential** and matches Conjecture B's scope: without it the
existential is *also* false — on `K_d` + many pendants (`K₁₂+30`) the pendant edges lie in no triangle,
so `triangleGraph G` is disconnected and `max gap < 0` over the whole eigenspace; but there
`λ₂(T(G)) = 0 ≤ λ₂(G)` trivially (outside the conjecture). With `triangleGraph G` connected,
`max gap ≥ 0` on all tested graphs. -/
theorem triEnergy_le_RHS_exists (lam mE : ℝ)
    (hTconn : (triangleGraph G).Connected)
    (f₀ : V → ℝ) (hf₀norm : ∑ v : V, (f₀ v) ^ 2 = 1) (hf₀perp : ∑ v : V, f₀ v = 0)
    (hf₀eig : (G.lapMatrix ℝ).mulVec f₀ = lam • f₀) :
    ∃ f : V → ℝ, (∑ v : V, (f v) ^ 2 = 1) ∧ (∑ v : V, f v = 0)
      ∧ (G.lapMatrix ℝ).mulVec f = lam • f
      ∧ triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := by
  -- The witness `f₀` itself works: regime architecture gives `gapEnergy f₀ ≥ 0`.
  refine ⟨f₀, hf₀norm, hf₀perp, hf₀eig, ?_⟩
  have haggr : 0 ≤ aggregateSlack G f₀ lam := by
    have := aggregate_triangle_poincare G f₀ lam hf₀eig
    simp only [aggregateSlack]; linarith
  have hgap := gapEnergy_nonneg G f₀ lam mE hTconn hf₀eig haggr
  simp only [gapEnergy] at hgap; linarith

/-- **Conjecture B — triangle-energy lift inequality (EXISTENTIAL).** Given a unit Fiedler `f₀`
(`L_G f₀ = λ f₀`, `‖f₀‖² = 1`, `f₀ ⊥ 1`), there exists a unit Fiedler `f` for the same `λ` with
`triEnergy G f ≤ 2λ(2fᵀDf − λ − S²/mE)` (`= 2·λ₂G`). This is the form that implies `λ₂(T(G)) ≤ λ₂(G)`
(Conjecture B) via the projected Fiedler lift — Courant–Fischer on `T(G)` needs *one* good test
vector, so *one* good Fiedler suffices. The earlier *universal* `conjectureB_lift` (`∀ f`) was FALSE on
degenerate `λ₂` (`triEnergy_le_RHS_exists`); this existential form is the correct replacement, and
`conjectureB_lift` depends on the single sorry `triEnergy_le_RHS_exists`. The `hTconn` hypothesis
(triangleGraph connected) matches Conjecture B's scope and is essential (see `triEnergy_le_RHS_exists`). -/
theorem conjectureB_lift (lam mE : ℝ)
    (hTconn : (triangleGraph G).Connected)
    (f₀ : V → ℝ) (hf₀norm : ∑ v : V, (f₀ v) ^ 2 = 1) (hf₀perp : ∑ v : V, f₀ v = 0)
    (hf₀eig : (G.lapMatrix ℝ).mulVec f₀ = lam • f₀) :
    ∃ f : V → ℝ, (∑ v : V, (f v) ^ 2 = 1) ∧ (∑ v : V, f v = 0)
      ∧ (G.lapMatrix ℝ).mulVec f = lam • f
      ∧ triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) :=
  triEnergy_le_RHS_exists G lam mE hTconn f₀ hf₀norm hf₀perp hf₀eig

/-- **Conjecture B (graph statement).** For connected `G` with `T(G)` connected,
`λ₂(T(G)) ≤ λ₂(G)`. Reduces to `conjectureB_lift` via the projected Fiedler lift
`h' = Bᵀf − (S/m)1_E ⊥ 1_E` together with `t_ab ≤ min(d_a,d_b)−1`
(`triCount_le_min_degree_sub_one`); that lift reduction is not yet formalised. -/
theorem conjectureB (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (hTV : Fintype.card (G.edgeSet) ≥ 2) (hTconn : (triangleGraph G).Connected) :
    algebraicConnectivity (triangleGraph G) hTV ≤ algebraicConnectivity G hV := by
  sorry

end Topostability
