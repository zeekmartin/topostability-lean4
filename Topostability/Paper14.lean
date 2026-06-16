import Topostability.Defs
import Topostability.Shared
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.MeanInequalities

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Fiedler hub-flatness (general eigenvector form).**

For any unit eigenvector `f` of the graph Laplacian `L_G` with eigenvalue `lam`
(`L_G f = lam • f`, `∑_v f v² = 1`), and any vertex `v` whose degree differs from
`lam`,
`f v² ≤ d_v / (d_v − lam)²`.

Proof: the eigen-equation at `v` gives `∑_{u∈N(v)} f u = (d_v − lam) · f v`;
Cauchy–Schwarz gives `(∑_{u∈N(v)} f u)² ≤ d_v · ∑_{u∈N(v)} f u² ≤ d_v · 1`; combining,
`(d_v − lam)² · f v² ≤ d_v`. Only the eigen-equation and `‖f‖ = 1` are used —
neither connectivity nor `f ⊥ 1`. Applying it with `lam = algebraicConnectivity G`
(`λ₂`) gives the hub-flatness bound for the Fiedler vector: at hubs `d_v ≥ 2λ₂` it
yields `f v² ≤ 4 / d_v`. -/
theorem eigenvector_hub_flatness
    (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hnorm : ∑ u : V, (f u) ^ 2 = 1)
    (v : V) (hdv : (G.degree v : ℝ) ≠ lam) :
    (f v) ^ 2 ≤ (G.degree v : ℝ) / ((G.degree v : ℝ) - lam) ^ 2 := by
  -- Step 1: the eigen-equation at `v`, expanded via L = D - A.
  have hv := congr_fun heig v
  simp only [SimpleGraph.lapMatrix, Matrix.sub_mulVec, Pi.sub_apply,
    SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.degMatrix,
    Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hv
  -- hv : (d_v) * f v - ∑_{u ∈ N(v)} f u = lam * f v
  have key : ∑ u ∈ G.neighborFinset v, f u = ((G.degree v : ℝ) - lam) * f v := by
    have e : ((G.degree v : ℝ) - lam) * f v
        = (G.degree v : ℝ) * f v - lam * f v := by ring
    rw [e]; linarith [hv]
  -- Step 2: Cauchy–Schwarz on the neighbour sum.
  have hcs : (∑ u ∈ G.neighborFinset v, f u) ^ 2
      ≤ (G.degree v : ℝ) * ∑ u ∈ G.neighborFinset v, (f u) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (G.neighborFinset v) (fun _ => (1 : ℝ)) f
    simp only [one_mul, one_pow] at h
    have hc : ∑ _u ∈ G.neighborFinset v, (1 : ℝ) = (G.degree v : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        SimpleGraph.card_neighborFinset_eq_degree]
    rwa [hc] at h
  -- Step 3: neighbour energy ≤ total energy = 1.
  have hsub : ∑ u ∈ G.neighborFinset v, (f u) ^ 2 ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _)
  -- Step 4: assemble  (d_v - lam)² · f v² ≤ d_v  and divide.
  have hne : (G.degree v : ℝ) - lam ≠ 0 := sub_ne_zero.mpr hdv
  have hpos : 0 < ((G.degree v : ℝ) - lam) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) ((pow_ne_zero 2 hne).symm)
  have hfinal : ((G.degree v : ℝ) - lam) ^ 2 * (f v) ^ 2 ≤ (G.degree v : ℝ) := by
    have e1 : ((G.degree v : ℝ) - lam) ^ 2 * (f v) ^ 2
        = (∑ u ∈ G.neighborFinset v, f u) ^ 2 := by rw [key]; ring
    rw [e1]
    calc (∑ u ∈ G.neighborFinset v, f u) ^ 2
        ≤ (G.degree v : ℝ) * ∑ u ∈ G.neighborFinset v, (f u) ^ 2 := hcs
      _ ≤ (G.degree v : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = (G.degree v : ℝ) := mul_one _
  rw [le_div_iff₀ hpos, mul_comm]
  exact hfinal

/-- **Fiedler hub-flatness.** Specialisation of `eigenvector_hub_flatness` to the
algebraic connectivity `λ₂`: for a unit Fiedler vector `f` (`L_G f = λ₂ • f`,
`∑_v f v² = 1`) and any vertex `v` with `d_v ≠ λ₂`,
`f v² ≤ d_v / (d_v − λ₂)²`. -/
theorem fiedler_hub_flatness
    (hV : Fintype.card V ≥ 2) (f : V → ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f)
    (hnorm : ∑ u : V, (f u) ^ 2 = 1)
    (v : V) (hdv : (G.degree v : ℝ) ≠ algebraicConnectivity G hV) :
    (f v) ^ 2 ≤ (G.degree v : ℝ) /
      ((G.degree v : ℝ) - algebraicConnectivity G hV) ^ 2 :=
  eigenvector_hub_flatness G f (algebraicConnectivity G hV) heig hnorm v hdv

end Topostability
