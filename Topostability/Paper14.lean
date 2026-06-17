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

/-- The eigenvector equation at a single vertex: `∑_{u∈N(v)} f u = (d_v − λ)·f v`. -/
lemma lapMatrix_eigen_neighbor_sum {f : V → ℝ} {lam : ℝ}
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) (v : V) :
    ∑ u ∈ G.neighborFinset v, f u = ((G.degree v : ℝ) - lam) * f v := by
  have hv := congr_fun heig v
  simp only [SimpleGraph.lapMatrix, Matrix.sub_mulVec, Pi.sub_apply,
    SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.degMatrix,
    Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hv
  have e : ((G.degree v : ℝ) - lam) * f v
      = (G.degree v : ℝ) * f v - lam * f v := by ring
  rw [e]; linarith [hv]

/-- **Gradient hub-flatness engine.** For any unit eigenvector `f` of `L_G`
(`L_G f = λ • f`, `∑_v f v² = 1`) and any two vertices `a b`,
`((d_a − λ)·f_a − (d_b − λ)·f_b)² ≤ |N(a) △ N(b)|`, with the symmetric difference
written as `(N(a)\N(b)) ∪ (N(b)\N(a))`. Proof: subtract the eigen-equations at `a`
and `b` — the common neighbours cancel, leaving a signed sum over `N(a) △ N(b)` — then
Cauchy–Schwarz with `‖f‖ = 1`. No degree or adjacency hypothesis. -/
theorem fiedler_neighbor_diff_sq {f : V → ℝ} {lam : ℝ}
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hnorm : ∑ u : V, (f u) ^ 2 = 1) (a b : V) :
    (((G.degree a : ℝ) - lam) * f a - ((G.degree b : ℝ) - lam) * f b) ^ 2
      ≤ ((G.neighborFinset a \ G.neighborFinset b).card : ℝ)
        + (G.neighborFinset b \ G.neighborFinset a).card := by
  set s := G.neighborFinset a with hs
  set t := G.neighborFinset b with ht
  set D := (s \ t) ∪ (t \ s) with hDdef
  set p : V → ℝ := fun u => if u ∈ s then (1 : ℝ) else -1 with hp
  have hdisj : Disjoint (s \ t) (t \ s) :=
    Finset.disjoint_left.mpr fun x hx hx2 =>
      (Finset.mem_sdiff.mp hx2).2 (Finset.mem_sdiff.mp hx).1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D p f
  -- (A): the signed sum over the symmetric difference is ∑_{N a} f − ∑_{N b} f.
  have hA : ∑ u ∈ D, p u * f u = (∑ u ∈ s, f u) - ∑ u ∈ t, f u := by
    have hsplit : (∑ u ∈ s, f u) - ∑ u ∈ t, f u
        = (∑ u ∈ s \ t, f u) - ∑ u ∈ t \ s, f u := by
      rw [← Finset.sum_inter_add_sum_diff s t f, ← Finset.sum_inter_add_sum_diff t s f,
          Finset.inter_comm t s]; ring
    rw [hsplit, hDdef, Finset.sum_union hdisj, sub_eq_add_neg]
    congr 1
    · exact Finset.sum_congr rfl fun u hu => by
        simp only [hp]; rw [if_pos (Finset.mem_sdiff.mp hu).1, one_mul]
    · rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun u hu => by
        simp only [hp]; rw [if_neg (Finset.mem_sdiff.mp hu).2]; ring
  -- (B): ∑ over D of p² is the cardinality (p = ±1).
  have hB : ∑ u ∈ D, (p u) ^ 2 = (D.card : ℝ) := by
    have h1 : ∀ u ∈ D, (p u) ^ 2 = (1 : ℝ) := fun u _ => by
      simp only [hp]; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- (C): neighbour energy ≤ total = 1.
  have hC : ∑ u ∈ D, (f u) ^ 2 ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _)
  -- (D): the subtracted eigen-equations.
  have hD2 : (∑ u ∈ s, f u) - ∑ u ∈ t, f u
      = ((G.degree a : ℝ) - lam) * f a - ((G.degree b : ℝ) - lam) * f b := by
    rw [hs, ht, lapMatrix_eigen_neighbor_sum G heig a, lapMatrix_eigen_neighbor_sum G heig b]
  have hcard : (D.card : ℝ) = ((s \ t).card : ℝ) + ((t \ s).card : ℝ) := by
    rw [hDdef, Finset.card_union_of_disjoint hdisj]; push_cast; ring
  rw [hA, hD2, hB] at hcs
  calc (((G.degree a : ℝ) - lam) * f a - ((G.degree b : ℝ) - lam) * f b) ^ 2
      ≤ (D.card : ℝ) * ∑ u ∈ D, (f u) ^ 2 := hcs
    _ ≤ (D.card : ℝ) * 1 := mul_le_mul_of_nonneg_left hC (by positivity)
    _ = (D.card : ℝ) := mul_one _
    _ = ((s \ t).card : ℝ) + ((t \ s).card : ℝ) := hcard

/-- **Fiedler gradient hub-flatness (equal-degree case).** If `d_a = d_b` and
`d_a ≠ λ`, then `(f_a − f_b)² ≤ |N(a) △ N(b)| / (d_a − λ)²`. (The general `min(d_a,d_b)`
form holds empirically; this rigorous equal-degree version is the one used on the dense
bulk, where degrees are equal and the symmetric difference is small.) -/
theorem fiedler_gradient_hub_flatness {f : V → ℝ} {lam : ℝ}
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hnorm : ∑ u : V, (f u) ^ 2 = 1) (a b : V)
    (hdeg : G.degree a = G.degree b) (hne : (G.degree a : ℝ) ≠ lam) :
    (f a - f b) ^ 2 ≤
      (((G.neighborFinset a \ G.neighborFinset b).card : ℝ)
        + (G.neighborFinset b \ G.neighborFinset a).card)
      / ((G.degree a : ℝ) - lam) ^ 2 := by
  have eng := fiedler_neighbor_diff_sq G heig hnorm a b
  have hdb : (G.degree b : ℝ) = (G.degree a : ℝ) := by exact_mod_cast hdeg.symm
  rw [hdb] at eng
  have factor : ((G.degree a : ℝ) - lam) * f a - ((G.degree a : ℝ) - lam) * f b
      = ((G.degree a : ℝ) - lam) * (f a - f b) := by ring
  rw [factor, mul_pow] at eng
  have hne0 : (G.degree a : ℝ) - lam ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < ((G.degree a : ℝ) - lam) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) ((pow_ne_zero 2 hne0).symm)
  rw [le_div_iff₀ hpos, mul_comm]
  exact eng

/-- **Cauchy–Schwarz core.** For unit `f` (`∑ f² = 1`) and finsets `s t`,
`(∑_s f − ∑_t f)² ≤ |s \ t| + |t \ s|`. The common part of `s,t` cancels; the rest is a
signed sum over the symmetric difference, bounded by Cauchy–Schwarz. -/
lemma signed_sum_diff_sq_le {f : V → ℝ} (hnorm : ∑ u : V, (f u) ^ 2 = 1) (s t : Finset V) :
    ((∑ u ∈ s, f u) - ∑ u ∈ t, f u) ^ 2
      ≤ ((s \ t).card : ℝ) + (t \ s).card := by
  set D := (s \ t) ∪ (t \ s) with hDdef
  set p : V → ℝ := fun u => if u ∈ s then (1 : ℝ) else -1 with hp
  have hdisj : Disjoint (s \ t) (t \ s) :=
    Finset.disjoint_left.mpr fun x hx hx2 =>
      (Finset.mem_sdiff.mp hx2).2 (Finset.mem_sdiff.mp hx).1
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D p f
  have hA : ∑ u ∈ D, p u * f u = (∑ u ∈ s, f u) - ∑ u ∈ t, f u := by
    have hsplit : (∑ u ∈ s, f u) - ∑ u ∈ t, f u
        = (∑ u ∈ s \ t, f u) - ∑ u ∈ t \ s, f u := by
      rw [← Finset.sum_inter_add_sum_diff s t f, ← Finset.sum_inter_add_sum_diff t s f,
          Finset.inter_comm t s]; ring
    rw [hsplit, hDdef, Finset.sum_union hdisj, sub_eq_add_neg]
    congr 1
    · exact Finset.sum_congr rfl fun u hu => by
        simp only [hp]; rw [if_pos (Finset.mem_sdiff.mp hu).1, one_mul]
    · rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun u hu => by
        simp only [hp]; rw [if_neg (Finset.mem_sdiff.mp hu).2]; ring
  have hB : ∑ u ∈ D, (p u) ^ 2 = (D.card : ℝ) := by
    have h1 : ∀ u ∈ D, (p u) ^ 2 = (1 : ℝ) := fun u _ => by
      simp only [hp]; split_ifs <;> norm_num
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hC : ∑ u ∈ D, (f u) ^ 2 ≤ 1 := by
    rw [← hnorm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _)
  have hcard : (D.card : ℝ) = ((s \ t).card : ℝ) + ((t \ s).card : ℝ) := by
    rw [hDdef, Finset.card_union_of_disjoint hdisj]; push_cast; ring
  rw [hA, hB] at hcs
  calc ((∑ u ∈ s, f u) - ∑ u ∈ t, f u) ^ 2
      ≤ (D.card : ℝ) * ∑ u ∈ D, (f u) ^ 2 := hcs
    _ ≤ (D.card : ℝ) * 1 := mul_le_mul_of_nonneg_left hC (by positivity)
    _ = (D.card : ℝ) := mul_one _
    _ = ((s \ t).card : ℝ) + ((t \ s).card : ℝ) := hcard

/-- **Fiedler gradient hub-flatness (adjacent, sharp `+1`).** For `a ~ b` with
`d_a = d_b = d` and `d − λ + 1 ≠ 0`,
`(f_a − f_b)² ≤ |N(a) △ N(b)| / (d − λ + 1)²`. Adjacency moves `b∈N(a)`, `a∈N(b)` to the
other side, sharpening the denominator from `(d−λ)²` to `(d−λ+1)²`. -/
theorem fiedler_gradient_hub_flatness_adj {f : V → ℝ} {lam : ℝ}
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hnorm : ∑ u : V, (f u) ^ 2 = 1) (a b : V)
    (hab : G.Adj a b) (hdeg : G.degree a = G.degree b)
    (hne : (G.degree a : ℝ) - lam + 1 ≠ 0) :
    (f a - f b) ^ 2 ≤
      (((G.neighborFinset a \ G.neighborFinset b).card : ℝ)
        + (G.neighborFinset b \ G.neighborFinset a).card)
      / ((G.degree a : ℝ) - lam + 1) ^ 2 := by
  have hbNa : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hab
  have haNb : a ∈ G.neighborFinset b := (G.mem_neighborFinset b a).mpr hab.symm
  have ea : ∑ u ∈ (G.neighborFinset a).erase b, f u
      = ((G.degree a : ℝ) - lam) * f a - f b := by
    have h := Finset.sum_erase_add (G.neighborFinset a) f hbNa
    rw [lapMatrix_eigen_neighbor_sum G heig a] at h; linarith [h]
  have eb : ∑ u ∈ (G.neighborFinset b).erase a, f u
      = ((G.degree b : ℝ) - lam) * f b - f a := by
    have h := Finset.sum_erase_add (G.neighborFinset b) f haNb
    rw [lapMatrix_eigen_neighbor_sum G heig b] at h; linarith [h]
  have hdb : (G.degree b : ℝ) = (G.degree a : ℝ) := by exact_mod_cast hdeg.symm
  have hid : (∑ u ∈ (G.neighborFinset a).erase b, f u)
              - ∑ u ∈ (G.neighborFinset b).erase a, f u
            = ((G.degree a : ℝ) - lam + 1) * (f a - f b) := by
    rw [ea, eb, hdb]; ring
  have core := signed_sum_diff_sq_le hnorm ((G.neighborFinset a).erase b)
    ((G.neighborFinset b).erase a)
  rw [hid, mul_pow] at core
  have sub1 : ((G.neighborFinset a).erase b) \ ((G.neighborFinset b).erase a)
      ⊆ G.neighborFinset a \ G.neighborFinset b := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_erase] at hx ⊢
    obtain ⟨⟨_, hxNa⟩, hxnot⟩ := hx
    have hxnea : x ≠ a := ((G.mem_neighborFinset a x).mp hxNa).ne'
    exact ⟨hxNa, fun hxNb => hxnot ⟨hxnea, hxNb⟩⟩
  have sub2 : ((G.neighborFinset b).erase a) \ ((G.neighborFinset a).erase b)
      ⊆ G.neighborFinset b \ G.neighborFinset a := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_erase] at hx ⊢
    obtain ⟨⟨_, hxNb⟩, hxnot⟩ := hx
    have hxneb : x ≠ b := ((G.mem_neighborFinset b x).mp hxNb).ne'
    exact ⟨hxNb, fun hxNa => hxnot ⟨hxneb, hxNa⟩⟩
  have hcardle :
      (((G.neighborFinset a).erase b \ (G.neighborFinset b).erase a).card : ℝ)
        + ((G.neighborFinset b).erase a \ (G.neighborFinset a).erase b).card
      ≤ ((G.neighborFinset a \ G.neighborFinset b).card : ℝ)
        + (G.neighborFinset b \ G.neighborFinset a).card := by
    have c1 := Finset.card_le_card sub1
    have c2 := Finset.card_le_card sub2
    exact_mod_cast add_le_add c1 c2
  have hpos : 0 < ((G.degree a : ℝ) - lam + 1) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) ((pow_ne_zero 2 hne).symm)
  rw [le_div_iff₀ hpos, mul_comm]
  calc ((G.degree a : ℝ) - lam + 1) ^ 2 * (f a - f b) ^ 2
      ≤ (((G.neighborFinset a).erase b \ (G.neighborFinset b).erase a).card : ℝ)
        + ((G.neighborFinset b).erase a \ (G.neighborFinset a).erase b).card := core
    _ ≤ _ := hcardle

end Topostability
