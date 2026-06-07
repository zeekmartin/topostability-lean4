import Topostability.Defs
import Topostability.Shared
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Sort

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Paper 12 proof infrastructure

The proof of `lambda2_lower_bound` follows three steps:

1. **Cut multiplication** (`cut_multiplication`): If `tauG G ≥ k`, every vertex cut
   `(S, Sᶜ)` has at least `k + 1` boundary edges.
2. **Conductance bound** (`conductance_lower_bound`): Combined with `vol(S) ≤ (n/2) · Δ`,
   this gives `h(G) ≥ 2(k+1)/(n · Δ)`.
3. **Cheeger inequality** (`cheeger_inequality`): `λ₂ ≥ h(G)²/(2Δ)`, which yields
   `λ₂ ≥ 2(k+1)²/(n² · Δ³)`.

Steps 2–3 require spectral graph theory infrastructure (conductance, Cheeger) not yet
in Mathlib. Each gap is documented below. -/

/-- The edge boundary of a vertex set `S`: directed edges from `S` to `Sᶜ`.
Each undirected boundary edge `{u,v}` with `u ∈ S, v ∉ S` appears exactly once
as `(u, v)` in this finset. Uses `SimpleGraph.interedges` from Mathlib. -/
def edgeBoundary (S : Finset V) : Finset (V × V) :=
  G.interedges S Sᶜ

/-- **Paper 12, Lemma 1 (Cut multiplication)**: If `tauG G ≥ k`, then every vertex cut
in a connected graph has at least `k + 1` boundary edges.

*Proof*: Pick a boundary edge `(u, v)` with `u ∈ S, v ∉ S` (exists by connectivity).
Since `triCount G u v ≥ tauG G ≥ k`, there are ≥ k common neighbors. Map each common
neighbor `w` to `(w, v)` if `w ∈ S`, or `(u, w)` if `w ∉ S`. This injection, together
with the original edge `(u, v)`, gives `k + 1` distinct boundary edges. -/
lemma cut_multiplication
    (hconn : G.Connected) (k : ℕ) (hk : tauG G ≥ k)
    (S : Finset V) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    k + 1 ≤ (edgeBoundary G S).card := by
  -- Step 1: Find a boundary edge via connectivity + Walk.exists_boundary_dart
  obtain ⟨a, haS⟩ := hS
  obtain ⟨b, hbSc⟩ := hSc
  have hbS : b ∉ S := Finset.mem_compl.mp hbSc
  obtain ⟨p⟩ := hconn.preconnected a b
  obtain ⟨d, -, hdS, hdSc⟩ :=
    p.exists_boundary_dart (↑S) (Finset.mem_coe.mpr haS) (mt Finset.mem_coe.mp hbS)
  set u := d.fst
  set v := d.snd
  have huS : u ∈ S := Finset.mem_coe.mp hdS
  have hvS : v ∉ S := mt Finset.mem_coe.mpr hdSc
  have hadj : G.Adj u v := d.adj
  -- Step 2: k ≤ |common neighbors|, since tauG ≤ triCount for each edge
  set CN := G.neighborFinset u ∩ G.neighborFinset v
  have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj
  have hne : G.edgeFinset.Nonempty := ⟨_, hmem⟩
  have hk_cn : k ≤ CN.card := by
    have h1 := Finset.inf'_le (triCountSym2 G) hmem
    simp only [triCountSym2, Sym2.lift_mk, triCount] at h1
    simp only [tauG, dif_pos hne] at hk
    exact le_trans hk h1
  -- Step 3: Define injection f from common neighbors to boundary edges
  let f : V → V × V := fun w => if w ∈ S then (w, v) else (u, w)
  -- f maps CN into edgeBoundary
  have hf_mem : ∀ w ∈ CN, f w ∈ edgeBoundary G S := by
    intro w hw
    simp only [CN, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
    change f w ∈ G.interedges S Sᶜ
    dsimp only [f]
    by_cases hwS : w ∈ S <;> simp only [hwS, ↓reduceIte]
    · exact Rel.mk_mem_interedges_iff.mpr ⟨hwS, Finset.mem_compl.mpr hvS, hw.2.symm⟩
    · exact Rel.mk_mem_interedges_iff.mpr ⟨huS, Finset.mem_compl.mpr hwS, hw.1⟩
  -- f is injective on CN
  have hf_inj : Set.InjOn f ↑CN := by
    intro w₁ hw₁ w₂ hw₂ hfeq
    simp only [Finset.mem_coe, CN, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw₁ hw₂
    dsimp only [f] at hfeq
    by_cases h₁ : w₁ ∈ S <;> by_cases h₂ : w₂ ∈ S <;>
        simp only [h₁, h₂, ↓reduceIte] at hfeq
    · exact (Prod.mk.inj hfeq).1
    · exfalso; rw [(Prod.mk.inj hfeq).1] at hw₁; exact hw₁.1.ne rfl
    · exfalso; rw [← (Prod.mk.inj hfeq).1] at hw₂; exact hw₂.1.ne rfl
    · exact (Prod.mk.inj hfeq).2
  -- (u, v) is in edgeBoundary but not in the image of f
  have huv_mem : (u, v) ∈ edgeBoundary G S :=
    Rel.mk_mem_interedges_iff.mpr ⟨huS, Finset.mem_compl.mpr hvS, hadj⟩
  have huv_notin : (u, v) ∉ CN.image f := by
    simp only [Finset.mem_image]
    rintro ⟨w, hwCN, hweq⟩
    simp only [CN, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hwCN
    dsimp only [f] at hweq
    by_cases hwS : w ∈ S <;> simp only [hwS, ↓reduceIte] at hweq
    · rw [(Prod.mk.inj hweq).1] at hwCN; exact hwCN.1.ne rfl
    · rw [(Prod.mk.inj hweq).2] at hwCN; exact hwCN.2.ne rfl
  -- Step 4: Count — insert (u,v) into image gives k+1 elements inside edgeBoundary
  calc k + 1
    _ ≤ CN.card + 1 := Nat.add_le_add_right hk_cn 1
    _ = (CN.image f).card + 1 := by rw [Finset.card_image_of_injOn hf_inj]
    _ = (insert (u, v) (CN.image f)).card := (Finset.card_insert_of_notMem huv_notin).symm
    _ ≤ (edgeBoundary G S).card :=
        Finset.card_le_card (Finset.insert_subset huv_mem (fun e he => by
          obtain ⟨w, hwCN, rfl⟩ := Finset.mem_image.mp he; exact hf_mem w hwCN))

/-- The set of valid vertex cuts: nonempty proper subsets `S` with `|S| ≤ |V|/2`. -/
def validCuts : Finset (Finset V) :=
  Finset.univ.filter fun S => 0 < S.card ∧ 0 < Sᶜ.card ∧ S.card ≤ Fintype.card V / 2

/-- The edge expansion (conductance) of a graph: the minimum ratio
`|∂S| / |S|` over all valid vertex cuts `S`.

Note: the previous `⨅`-based definition was unsound for `ℝ`, because
`sInf ∅ = 0` causes false cuts (failing conditions) to contribute `0`,
making the infimum ≤ 0 unconditionally. This `Finset.inf'`-based definition
computes the true minimum over a finite set of valid cuts. -/
noncomputable def conductance (hV : Fintype.card V ≥ 2) : ℝ :=
  have hne : (validCuts (V := V)).Nonempty := by
    obtain ⟨v⟩ : Nonempty V := ⟨(Fintype.equivFin V).symm ⟨0, by omega⟩⟩
    exact ⟨{v}, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      by simp [Finset.card_singleton, Finset.card_compl]; omega⟩⟩
  (validCuts (V := V)).inf' hne fun S =>
    ↑(edgeBoundary G S).card / (↑S.card : ℝ)

/-- **Paper 12, Step 2**: If `tauG G ≥ k`, the conductance satisfies
`h(G) ≥ 2(k+1)/n`.

*Proof*: By `cut_multiplication`, `|∂S| ≥ k + 1` for every valid cut.
Since `|S| ≤ n/2`, cross-multiplying gives `2(k+1) · |S| ≤ |∂S| · n`,
hence `2(k+1)/n ≤ |∂S|/|S|`. The bound holds for all cuts, so it
holds for the minimum (conductance). -/
lemma conductance_lower_bound
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2) (k : ℕ)
    (hk : tauG G ≥ k) :
    (2 * (↑k + 1) : ℝ) / ↑(Fintype.card V) ≤ conductance G hV := by
  unfold conductance
  apply Finset.le_inf'
  intro S hS
  simp only [validCuts, Finset.mem_filter, Finset.mem_univ, true_and] at hS
  obtain ⟨hSpos, hScpos, hSle⟩ := hS
  have hSne : S.Nonempty := Finset.card_pos.mp hSpos
  have hScne : Sᶜ.Nonempty := Finset.card_pos.mp hScpos
  -- |∂S| ≥ k + 1 from cut_multiplication
  have hbound := cut_multiplication G hconn k hk S hSne hScne
  -- Real arithmetic: 2(k+1)/n ≤ |∂S|/|S|
  have hn_pos : (0 : ℝ) < ↑(Fintype.card V) := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hS_pos : (0 : ℝ) < ↑S.card := by exact_mod_cast hSpos
  rw [div_le_div_iff₀ hn_pos hS_pos]
  -- Goal: 2 * (↑k + 1) * ↑S.card ≤ ↑(edgeBoundary G S).card * ↑(Fintype.card V)
  have h1 : (k + 1 : ℝ) ≤ (edgeBoundary G S).card := by exact_mod_cast hbound
  have h2 : 2 * (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (show 2 * S.card ≤ Fintype.card V by omega)
  nlinarith [mul_le_mul h1 h2 (by positivity) (by positivity)]

/-! ### Test vector lemmas for the Cheeger inequality

For a cut `(S, Sᶜ)`, the test vector `x(v) = |Sᶜ|` if `v ∈ S`, `x(v) = -|S|`
if `v ∉ S` is orthogonal to the all-ones vector and has a Rayleigh quotient
that relates to the edge expansion. -/

/-- The cut test vector for a partition `(S, Sᶜ)`. -/
noncomputable def cutTestVec (S : Finset V) : V → ℝ := fun v =>
  if v ∈ S then (↑Sᶜ.card : ℝ) else -(↑S.card : ℝ)

/-- The cut test vector sums to zero: `Σᵥ x(v) = 0`. -/
lemma cutTestVec_sum_eq_zero (S : Finset V) :
    ∑ v : V, cutTestVec S v = 0 := by
  have h_split : ∑ v : V, cutTestVec S v =
      (∑ v ∈ S, cutTestVec S v) + ∑ v ∈ Sᶜ, cutTestVec S v := by
    rw [← Finset.sum_union disjoint_compl_right,
      Finset.union_compl S]
  have h_on_S : ∑ v ∈ S, cutTestVec S v = ↑S.card * ↑Sᶜ.card := by
    rw [Finset.sum_congr rfl (fun v hv => show cutTestVec S v = ↑Sᶜ.card by
      simp [cutTestVec, hv])]
    simp [Finset.sum_const, nsmul_eq_mul]
  have h_on_Sc : ∑ v ∈ Sᶜ, cutTestVec S v = -(↑Sᶜ.card * ↑S.card) := by
    rw [Finset.sum_congr rfl (fun v hv => show cutTestVec S v = -(↑S.card : ℝ) by
      simp [cutTestVec, Finset.mem_compl.mp hv])]
    simp [Finset.sum_const, nsmul_eq_mul, Finset.sum_neg_distrib]
  rw [h_split, h_on_S, h_on_Sc]; ring

/-- The squared norm of the cut test vector: `‖x‖² = n · |S| · |Sᶜ|`. -/
lemma cutTestVec_norm_sq (S : Finset V) :
    ∑ v : V, cutTestVec S v ^ 2 =
      ↑(Fintype.card V) * ↑S.card * ↑Sᶜ.card := by
  have h_split : ∑ v : V, cutTestVec S v ^ 2 =
      (∑ v ∈ S, cutTestVec S v ^ 2) + ∑ v ∈ Sᶜ, cutTestVec S v ^ 2 := by
    rw [← Finset.sum_union disjoint_compl_right,
      Finset.union_compl S]
  have h_on_S : ∑ v ∈ S, cutTestVec S v ^ 2 =
      ↑S.card * (↑Sᶜ.card : ℝ) ^ 2 := by
    rw [Finset.sum_congr rfl (fun v hv => show cutTestVec S v ^ 2 = (↑Sᶜ.card : ℝ) ^ 2 by
      simp [cutTestVec, hv])]
    simp [Finset.sum_const, nsmul_eq_mul]
  have h_on_Sc : ∑ v ∈ Sᶜ, cutTestVec S v ^ 2 =
      ↑Sᶜ.card * (↑S.card : ℝ) ^ 2 := by
    rw [Finset.sum_congr rfl (fun v hv => show cutTestVec S v ^ 2 = (↑S.card : ℝ) ^ 2 by
      simp [cutTestVec, Finset.mem_compl.mp hv])]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [h_split, h_on_S, h_on_Sc]
  have hn : (Fintype.card V : ℝ) = ↑S.card + ↑Sᶜ.card := by
    have : S.card + Sᶜ.card = Fintype.card V := by
      have := S.card_le_univ
      rw [Finset.card_compl]; omega
    exact_mod_cast this.symm
  rw [hn]; ring

/-- The quadratic form `xᵀLx` on the cut test vector equals `n² · |∂S|`.

Uses `lapMatrix_toLinearMap₂'`: `xᵀLx = (Σᵢⱼ [Adj i j] (xᵢ − xⱼ)²) / 2`.
For the cut vector, `(xᵢ − xⱼ)² = n²` on boundary edges and `0` otherwise.
Each undirected boundary edge appears twice in the double sum (once per
direction), so `xᵀLx = n² · 2|∂S| / 2 = n² · |∂S|`. -/
lemma cutTestVec_laplacian (S : Finset V) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) (cutTestVec S) (cutTestVec S) =
      ↑(Fintype.card V) ^ 2 * ↑(edgeBoundary G S).card := by
  rw [SimpleGraph.lapMatrix_toLinearMap₂']
  -- Key fact: |S| + |Sᶜ| = n
  have n_eq : (↑S.card : ℝ) + ↑Sᶜ.card = ↑(Fintype.card V) := by
    have : S.card + Sᶜ.card = Fintype.card V := by
      have := S.card_le_univ; rw [Finset.card_compl]; omega
    exact_mod_cast this
  -- Each (x_i - x_j)^2 is either 0 (same side) or n^2 (boundary)
  have hterm : ∀ i j : V,
      (if G.Adj i j then (cutTestVec S i - cutTestVec S j) ^ 2 else (0 : ℝ)) =
      if G.Adj i j ∧ (i ∈ S) ≠ (j ∈ S) then (↑(Fintype.card V) : ℝ) ^ 2 else 0 := by
    intro i j
    simp only [cutTestVec, ne_eq]
    by_cases hadj : G.Adj i j <;> by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [hadj, hi, hj] <;> nlinarith [n_eq]
  simp_rw [hterm]
  -- Factor: (∑∑ if boundary then n^2 else 0) / 2
  --       = n^2 * (∑∑ if boundary then 1 else 0) / 2
  -- Factor n^2 out and cancel with /2
  simp_rw [show ∀ i j : V,
    (if G.Adj i j ∧ (i ∈ S) ≠ (j ∈ S) then (↑(Fintype.card V) : ℝ) ^ 2 else (0 : ℝ)) =
    (↑(Fintype.card V) : ℝ) ^ 2 *
      (if G.Adj i j ∧ (i ∈ S) ≠ (j ∈ S) then (1 : ℝ) else 0) from
      fun i j => by split_ifs <;> ring]
  simp_rw [← Finset.mul_sum]
  rw [mul_div_assoc]
  congr 1
  -- Goal: (∑ i, ∑ j, if Adj i j ∧ (i∈S) ≠ (j∈S) then 1 else 0) / 2 = ↑|∂S|
  -- The indicator counts directed boundary pairs = 2 · |∂S|
  -- Split ≠ into two disjoint cases: (i∈S ∧ j∉S) ∨ (i∉S ∧ j∈S)
  have hsplit : ∀ i j : V,
      (if G.Adj i j ∧ (i ∈ S) ≠ (j ∈ S) then (1 : ℝ) else 0) =
      (if G.Adj i j ∧ i ∈ S ∧ j ∉ S then 1 else 0) +
      (if G.Adj i j ∧ i ∉ S ∧ j ∈ S then 1 else 0) := by
    intro i j
    by_cases hadj : G.Adj i j <;> by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
      simp [hadj, hi, hj]
  simp_rw [hsplit, Finset.sum_add_distrib]
  -- Two sums, each = |edgeBoundary G S|
  -- Count boundary pairs: ∑∑ indicator = 2 * |∂S|
  -- Helper: ℝ indicator double sum = ℕ interedges cardinality
  have hcount : ∀ (s : Finset V),
      ∑ i : V, ∑ j : V, (if G.Adj i j ∧ i ∈ s ∧ j ∉ s then (1 : ℝ) else 0) =
      ↑(G.interedges s sᶜ).card := by
    intro s
    -- Use sum_boole: ∑ if P then 1 else 0 = #{x | P x}
    rw [← Finset.sum_product', Finset.sum_boole]
    -- Strip ℕ→ℝ cast, then show filter sets equal
    norm_cast
    congr 1; ext ⟨i, j⟩
    unfold SimpleGraph.interedges
    simp only [Rel.mk_mem_interedges_iff, Finset.mem_compl,
      Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    tauto
  rw [hcount S]
  -- Convert second sum: i∉S ∧ j∈S ↔ i∈Sᶜ ∧ j∉Sᶜ
  simp_rw [show ∀ i j : V,
    (G.Adj i j ∧ i ∉ S ∧ j ∈ S) ↔ (G.Adj i j ∧ i ∈ Sᶜ ∧ j ∉ Sᶜ) from
      fun i j => by simp [Finset.mem_compl]]
  rw [hcount Sᶜ, compl_compl]
  -- Goal: (↑|interedges S Sᶜ| + ↑|interedges Sᶜ S|) / 2 = ↑|edgeBoundary S|
  -- Use symmetry: |interedges Sᶜ S| = |interedges S Sᶜ| = |edgeBoundary S|
  simp only [edgeBoundary, SimpleGraph.interedges]
  rw [Rel.card_interedges_comm G.symm Sᶜ S]
  ring

/-- **TASK 2**: Sweep cut — the level set `{v : f(v) ≥ t}`. -/
noncomputable def sweepCut (f : V → ℝ) (t : ℝ) : Finset V :=
  Finset.univ.filter (fun v => t ≤ f v)

/-! ### Sweep cut sub-lemmas (architecture for Cheeger hard direction)

The proof of `sweep_cut_bound` decomposes into the following chain:
1. Quadratic form = sum over edges (already proved as `cutTestVec_laplacian`)
2. Discrete coarea: ∑ |f(u)-f(v)| over edges = ∑ over thresholds of |∂S_t|
3. Cauchy–Schwarz on each boundary
4. Pigeonhole to find optimal threshold -/


/-- Telescoping sum: `s j - s i = ∑_{k ∈ Ico i j} (s(k+1) - s(k))`. -/
lemma telescope_sub (s : ℕ → ℝ) (i j : ℕ) (hij : i ≤ j) :
    s j - s i = ∑ k ∈ Finset.Ico i j, (s (k + 1) - s k) := by
  induction j with
  | zero => simp [Nat.le_zero.mp hij]
  | succ j ih =>
    by_cases heq : i = j + 1
    · subst heq; simp
    · rw [Finset.sum_Ico_succ_top (by omega : i ≤ j)]
      linarith [ih (by omega : i ≤ j)]


/-- A directed pair (u,v) crosses threshold k in the sorted ordering σ. -/
def crossing (σ : Fin (Fintype.card V) ≃ V) (k : ℕ) (u v : V) : Prop :=
  (σ.symm u).val ≤ k ∧ k < (σ.symm v).val

instance (σ : Fin (Fintype.card V) ≃ V) (k : ℕ) (u v : V) :
    Decidable (crossing σ k u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Crossing is exclusive: (u,v) and (v,u) can't both cross the same threshold. -/
lemma crossing_exclusive (σ : Fin (Fintype.card V) ≃ V) (k : ℕ) (u v : V) :
    ¬(crossing σ k u v ∧ crossing σ k v u) := by
  simp only [crossing]; omega


/-- When sortedGap ≠ 0, consecutive sorted values are strictly increasing. -/
lemma sortedGap_ne_zero_implies_strict
    (f : V → ℝ) (σ : Fin (Fintype.card V) ≃ V)
    (hσ : ∀ i j : Fin (Fintype.card V), i ≤ j → f (σ i) ≤ f (σ j))
    (k : Fin (Fintype.card V - 1))
    (hgap : f (σ ⟨k.val + 1, by omega⟩) - f (σ ⟨k.val, by omega⟩) ≠ 0) :
    f (σ ⟨k.val, by omega⟩) < f (σ ⟨k.val + 1, by omega⟩) := by
  have hle := hσ ⟨k.val, by omega⟩ ⟨k.val + 1, by omega⟩
    (Fin.le_def.mpr (by simp only [Fin.val_mk]; omega))
  exact lt_of_le_of_ne hle (fun h => hgap (by linarith))

/-- Crossing pairs (with one specific direction) biject to boundary edges. -/
lemma crossing_card_eq_boundary_card
    (f : V → ℝ) (σ : Fin (Fintype.card V) ≃ V)
    (hσ : ∀ i j : Fin (Fintype.card V), i ≤ j → f (σ i) ≤ f (σ j))
    (k : Fin (Fintype.card V - 1))
    (hstrict : f (σ ⟨k.val, by omega⟩) < f (σ ⟨k.val + 1, by omega⟩)) :
    (Finset.univ.filter (fun e : V × V =>
      G.Adj e.1 e.2 ∧ crossing σ k.val e.1 e.2)).card =
    (edgeBoundary G (Finset.univ.filter fun w =>
      f w ≥ f (σ ⟨k.val + 1, by omega⟩))).card := by
  -- Bijection: (u,v) with Adj u v, u below k, v above k+1
  -- ↔ (u,v) ∈ edgeBoundary S where S = {w | f w ≥ f(σ(k+1))}
  -- edgeBoundary S = interedges S Sᶜ = {(a,b) | a ∈ S, b ∈ Sᶜ, Adj a b}
  -- crossing k u v means u ≤ k < v in sorted order
  -- → f u ≤ f(σ k) < f(σ(k+1)) ≤ f v → u ∈ Sᶜ, v ∈ S
  -- So (u,v) maps to... (v,u) ∈ interedges S Sᶜ? No: u ∈ Sᶜ, v ∈ S.
  -- interedges S Sᶜ has first component ∈ S, second ∈ Sᶜ.
  -- So (v,u) ∈ interedges S Sᶜ. Bijection: (u,v) ↦ (v,u).
  apply Finset.card_bij (fun e _ => (e.2, e.1))
  · -- Maps into edgeBoundary
    intro ⟨u, v⟩ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨hadj, hu, hv⟩ := he
    simp only [edgeBoundary]
    unfold SimpleGraph.interedges
    rw [Rel.mk_mem_interedges_iff]
    refine ⟨?_, ?_, hadj.symm⟩
    · -- v ∈ S: f v ≥ f(σ(k+1))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hσ ⟨k.val + 1, by omega⟩ (σ.symm v)
        (Fin.le_def.mpr (by simp only [Fin.val_mk]; omega))
      simp only [Equiv.apply_symm_apply] at this; exact this
    · -- u ∈ Sᶜ: f u < f(σ(k+1))
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      have := hσ (σ.symm u) ⟨k.val, by omega⟩
        (Fin.le_def.mpr (by simp only [Fin.val_mk]; omega))
      simp only [Equiv.apply_symm_apply] at this; linarith
  · -- Injective
    intro ⟨u₁, v₁⟩ _ ⟨u₂, v₂⟩ _ h
    simp only [Prod.mk.injEq] at h; ext <;> simp_all
  · -- Surjective
    intro ⟨a, b⟩ hab
    simp only [edgeBoundary] at hab
    unfold SimpleGraph.interedges at hab
    rw [Rel.mk_mem_interedges_iff] at hab
    obtain ⟨ha_in, hb_out, hadj⟩ := hab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha_in
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hb_out
    refine ⟨(b, a), ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, crossing]
    refine ⟨hadj.symm, ?_, ?_⟩
    · -- b below: σ⁻¹(b) ≤ k
      by_contra h; push_neg at h
      have := hσ ⟨k.val + 1, by omega⟩ (σ.symm b)
        (Fin.le_def.mpr (by simp; omega))
      simp only [Equiv.apply_symm_apply] at this; linarith
    · -- a above: k < σ⁻¹(a)
      by_contra h; push_neg at h
      have := hσ (σ.symm a) ⟨k.val, by omega⟩
        (Fin.le_def.mpr (by simp; exact h))
      simp only [Equiv.apply_symm_apply] at this; linarith

/-- **Sub-lemma 2**: Discrete coarea — for each edge, |f(u)-f(v)| equals
the number of level-set thresholds (at sorted vertex values) that the
edge crosses. Summing over edges and exchanging gives: edge sum of
|f(u)-f(v)| = threshold sum of boundary sizes.

For the Cheeger proof, only the inequality `∑_edges |diff| ≤ ...` is
needed, which follows from this identity. The discrete coarea formula
is a standard result in combinatorial analysis.

Uses `crossing`, `crossing_exclusive`, `telescope_sub`, `Finset.sum_comm`. -/
lemma discrete_coarea (f : V → ℝ)
    (σ : Fin (Fintype.card V) ≃ V)
    (hσ : ∀ i j, i ≤ j → f (σ i) ≤ f (σ j))
    (hn : Fintype.card V ≥ 2) :
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => |f u - f v|,
        fun u v => by simp only [abs_sub_comm]⟩ e =
      ∑ k : Fin (Fintype.card V - 1),
        (f (σ ⟨k.val + 1, by omega⟩) - f (σ ⟨k.val, by omega⟩)) *
        ((edgeBoundary G (Finset.univ.filter fun w =>
          f w ≥ f (σ ⟨k.val + 1, by omega⟩))).card : ℝ) := by
  classical
  -- For each Sym2 edge {u,v}, apply telescope_sub to get:
  -- |f u - f v| = Σ_{k ∈ Ico (min_idx) (max_idx)} gap_k
  -- Then exchange sums and use crossing_card_eq_boundary_card

  -- Step 1: rewrite each edge using Sym2.ind + telescope_sub
  have hkey : ∀ (u v : V), s(u, v) ∈ G.edgeFinset →
      |f u - f v| =
      ∑ k : Fin (Fintype.card V - 1),
        (f (σ ⟨k.val + 1, by omega⟩) - f (σ ⟨k.val, by omega⟩)) *
        if k.val ∈ Finset.Ico
          (min (σ.symm u).val (σ.symm v).val)
          (max (σ.symm u).val (σ.symm v).val)
        then 1 else 0 := by
    intro u v _
    have hu := (σ.symm u).isLt
    have hv := (σ.symm v).isLt
    by_cases hij : (σ.symm u).val ≤ (σ.symm v).val
    · -- |f u - f v| = f v - f u (since f u ≤ f v)
      have hle : f u ≤ f v := by
        have h1 := hσ (σ.symm u) (σ.symm v) (Fin.le_def.mpr hij)
        simp only [Equiv.apply_symm_apply] at h1; exact h1
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      have hminmax : min (σ.symm u).val (σ.symm v).val = (σ.symm u).val ∧
                     max (σ.symm u).val (σ.symm v).val = (σ.symm v).val := by
        exact ⟨Nat.min_eq_left hij, Nat.max_eq_right hij⟩
      simp only [hminmax.1, hminmax.2]
      -- Use telescope_sub with s = fun k => if k < card V then f(σ⟨k,_⟩) else 0
      set s : ℕ → ℝ := fun k =>
        if hk : k < Fintype.card V then f (σ ⟨k, hk⟩) else 0
      have hsu : s (σ.symm u).val = f u := by simp [s, (σ.symm u).isLt, Equiv.apply_symm_apply]
      have hsv : s (σ.symm v).val = f v := by simp [s, (σ.symm v).isLt, Equiv.apply_symm_apply]
      have htel := telescope_sub s
        (σ.symm u).val (σ.symm v).val hij
      rw [hsv, hsu] at htel
      -- telescope gives f v - f u = Σ k ∈ Ico, (s(k+1) - s(k))
      rw [htel]
      -- Reindex: Ico sum → Fin (card V - 1) sum with indicator
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      simp only [s]
      apply Finset.sum_bij (fun k hk => ⟨k, by
          have := Finset.mem_Ico.mp hk
          have := (σ.symm v).isLt; omega⟩)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hk ⊢
        exact hk
      · intro a ha b hb h
        simp only [Fin.mk.injEq] at h; exact h
      · intro ⟨k, hk_lt⟩ hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hk
        exact ⟨k, Finset.mem_Ico.mpr hk, by simp⟩
      · intro k hk
        simp only [dif_pos (by have := Finset.mem_Ico.mp hk;
                                have := (σ.symm v).isLt; omega : k < Fintype.card V),
                   dif_pos (by have := Finset.mem_Ico.mp hk;
                                have := (σ.symm v).isLt; omega : k + 1 < Fintype.card V)]
    · push_neg at hij
      have hle : f v ≤ f u := by
        have h1 := hσ (σ.symm v) (σ.symm u)
          (Fin.le_def.mpr (by omega))
        simp only [Equiv.apply_symm_apply] at h1; exact h1
      rw [abs_of_nonneg (by linarith)]
      have hminmax : min (σ.symm u).val (σ.symm v).val = (σ.symm v).val ∧
                     max (σ.symm u).val (σ.symm v).val = (σ.symm u).val := by
        exact ⟨Nat.min_eq_right (by omega), Nat.max_eq_left (by omega)⟩
      simp only [hminmax.1, hminmax.2]
      -- symmetric to above case with u,v swapped
      set s : ℕ → ℝ := fun k =>
        if hk : k < Fintype.card V then f (σ ⟨k, hk⟩) else 0
      have hsu : s (σ.symm u).val = f u := by simp [s, (σ.symm u).isLt, Equiv.apply_symm_apply]
      have hsv : s (σ.symm v).val = f v := by simp [s, (σ.symm v).isLt, Equiv.apply_symm_apply]
      have htel := telescope_sub s
        (σ.symm v).val (σ.symm u).val (by omega)
      rw [hsu, hsv] at htel
      rw [htel]
      -- Symmetric reindex: Ico sum → Fin sum with indicator
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      simp only [s]
      apply Finset.sum_bij (fun k hk => ⟨k, by
          have := Finset.mem_Ico.mp hk
          have := (σ.symm u).isLt; omega⟩)
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hk ⊢
        exact hk
      · intro a ha b hb h
        simp only [Fin.mk.injEq] at h; exact h
      · intro ⟨k, hk_lt⟩ hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] at hk
        exact ⟨k, Finset.mem_Ico.mpr hk, by simp⟩
      · intro k hk
        simp only [dif_pos (by have := Finset.mem_Ico.mp hk;
                                have := (σ.symm u).isLt; omega : k < Fintype.card V),
                   dif_pos (by have := Finset.mem_Ico.mp hk;
                                have := (σ.symm u).isLt; omega : k + 1 < Fintype.card V)]
  -- Step 2: Lift hkey to Sym2 edges
  have hkey' : ∀ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => |f u - f v|,
        fun u v => by simp only [abs_sub_comm]⟩ e =
      ∑ k : Fin (Fintype.card V - 1),
        (f (σ ⟨k.val + 1, by omega⟩) - f (σ ⟨k.val, by omega⟩)) *
        if k.val ∈ Finset.Ico
          (min (σ.symm e.out.1).val (σ.symm e.out.2).val)
          (max (σ.symm e.out.1).val (σ.symm e.out.2).val)
        then 1 else 0 := by
    intro e he
    have hmk : s(e.out.1, e.out.2) = e := by rw [Sym2.mk, e.out_eq]
    conv_lhs => rw [← hmk, Sym2.lift_mk]
    exact hkey e.out.1 e.out.2 (by rwa [hmk])
  -- Step 3: Rewrite LHS using hkey', exchange sums
  rw [Finset.sum_congr rfl hkey']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  -- ∑ e ∈ edgeFinset, gap * indicator_k(e) = gap * |∂S_k|
  by_cases hgap : f (σ ⟨k.val + 1, by omega⟩) - f (σ ⟨k.val, by omega⟩) = 0
  · -- gap = 0: 0 * anything = 0
    simp [hgap]
  · -- gap ≠ 0: use crossing_card_eq_boundary_card
    have hstrict := sortedGap_ne_zero_implies_strict f σ hσ k hgap
    congr 1
    have hcast : ∀ e ∈ G.edgeFinset,
        (if k.val ∈ Finset.Ico
            (min (σ.symm e.out.1).val (σ.symm e.out.2).val)
            (max (σ.symm e.out.1).val (σ.symm e.out.2).val)
          then (1 : ℝ) else 0) =
        ↑(if k.val ∈ Finset.Ico
            (min (σ.symm e.out.1).val (σ.symm e.out.2).val)
            (max (σ.symm e.out.1).val (σ.symm e.out.2).val)
          then 1 else 0 : ℕ) := by intros; split_ifs <;> simp
    rw [Finset.sum_congr rfl hcast, ← Nat.cast_sum, Finset.sum_boole, Nat.cast_inj]
    rw [show (G.edgeFinset.filter (fun e =>
          k.val ∈ Finset.Ico
            (min (σ.symm e.out.1).val (σ.symm e.out.2).val)
            (max (σ.symm e.out.1).val (σ.symm e.out.2).val))).card =
        (Finset.univ.filter (fun e : V × V =>
          G.Adj e.1 e.2 ∧ crossing σ k.val e.1 e.2)).card from by
      symm
      apply Finset.card_bij (fun (p : V × V) _ => s(p.1, p.2))
      · -- membership: (u,v) with Adj ∧ crossing → s(u,v) ∈ edgeFinset.filter
        intro ⟨u, v⟩ h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, crossing] at h
        obtain ⟨hadj, h1, h2⟩ := h
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.mem_edgeFinset]; exact hadj
        · rw [Finset.mem_Ico, Nat.min_def, Nat.max_def]
          have hmk : s((s(u, v) : Sym2 V).out.1, (s(u, v) : Sym2 V).out.2) =
              s(u, v) := by rw [Sym2.mk, Quot.out_eq]
          rcases Sym2.eq_iff.mp hmk with ⟨ho1, ho2⟩ | ⟨ho1, ho2⟩ <;>
            (simp only [ho1, ho2]; split_ifs <;> omega)
      · -- injectivity
        intro ⟨u, v⟩ hu ⟨u', v'⟩ hu' heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, crossing] at hu hu'
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exfalso; simp only [Prod.fst, Prod.snd] at hu hu'
          obtain ⟨_, h1, h2⟩ := hu; obtain ⟨_, h3, h4⟩ := hu'; omega
      · -- surjectivity
        intro e he
        induction e using Sym2.ind with | _ a b =>
        simp only [Finset.mem_filter] at he
        have h_adj : G.Adj a b := by
          have := he.1; rw [SimpleGraph.mem_edgeFinset] at this; exact this
        have he_ico := he.2
        rw [Finset.mem_Ico, Nat.min_def, Nat.max_def] at he_ico
        have hmk : s((s(a, b) : Sym2 V).out.1, (s(a, b) : Sym2 V).out.2) =
            s(a, b) := by rw [Sym2.mk, Quot.out_eq]
        rcases Sym2.eq_iff.mp hmk with ⟨ho1, ho2⟩ | ⟨ho1, ho2⟩ <;>
          (simp only [ho1, ho2] at he_ico;
           by_cases hle : (σ.symm a).val ≤ (σ.symm b).val
           · refine ⟨(a, b), ?_, rfl⟩
             simp only [Finset.mem_filter, Finset.mem_univ, true_and, crossing]
             exact ⟨h_adj, by split_ifs at he_ico <;> omega⟩
           · push_neg at hle
             refine ⟨(b, a), ?_, Sym2.eq_swap⟩
             simp only [Finset.mem_filter, Finset.mem_univ, true_and, crossing]
             exact ⟨h_adj.symm, by split_ifs at he_ico <;> omega⟩)]
    exact crossing_card_eq_boundary_card G f σ (fun i j hij => hσ i j hij) k hstrict

--

/-- **Sub-lemma 3**: Cauchy–Schwarz on directed boundary edges. -/
lemma boundary_cauchy_schwarz (f : V → ℝ) (S : Finset V) :
    (∑ e ∈ edgeBoundary G S, |f e.1 - f e.2|) ^ 2 ≤
      ↑(edgeBoundary G S).card *
        ∑ e ∈ edgeBoundary G S, (f e.1 - f e.2) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := edgeBoundary G S)
    (f := fun e => |f e.1 - f e.2|)
  simp only [sq_abs] at h
  exact_mod_cast h

/-- Weighted edge-vertex sum: ∑ edges (f u² + f v²) = ∑ vertices degree(v) · f v².
Proved via dart fiber: ∑ darts f(d.fst)² = ∑_v degree(v) · f v². -/
lemma weighted_edge_vertex_sum (f : V → ℝ) :
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => f u ^ 2 + f v ^ 2, fun u v => by ring⟩ e =
      ∑ v : V, ↑(G.degree v) * f v ^ 2 := by
  -- Chain: ∑_edges (f u² + f v²) = ∑_darts f(d.fst)² = ∑_v degree(v) · f v²
  -- Step 1: ∑_darts f(d.fst)² = ∑_v degree(v) · f v²  (by fst fiber)
  classical
  have hdart_vertex : ∑ d : G.Dart, f d.fst ^ 2 =
      ∑ v : V, ↑(G.degree v) * f v ^ 2 := by
    -- ∑_d f(d.fst)² = ∑_v (∑_{d : d.fst = v} f(v)²) = ∑_v degree(v) · f(v)²
    have hfiber := Finset.sum_fiberwise_of_maps_to
      (g := fun (d : G.Dart) => d.fst) (f := fun d => f d.fst ^ 2)
      (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    conv_lhs => rw [← hfiber]
    congr 1 with v
    rw [Finset.sum_congr rfl (fun d (hd : d ∈ Finset.univ.filter _) => by
      rw [(Finset.mem_filter.mp hd).2])]
    simp only [Finset.sum_const, nsmul_eq_mul]
    congr 1; exact_mod_cast G.dart_fst_fiber_card_eq_degree v
  -- Step 2: ∑_edges (f u² + f v²) = ∑_darts f(d.fst)²  (by edge fiber)
  have hdart_edge : ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => f u ^ 2 + f v ^ 2, fun u v => by ring⟩ e =
      ∑ d : G.Dart, f d.fst ^ 2 := by
    classical
    -- ∑_darts f(d.fst)² = ∑_edges ∑_{d | d.edge = e} f(d.fst)²
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun (d : G.Dart) => d.edge) (s := Finset.univ)
      (t := G.edgeFinset) (fun d _ => SimpleGraph.mem_edgeFinset.mpr d.edge_mem)]
    -- For each edge e: fiber sum = f u² + f v²
    apply Finset.sum_congr rfl
    intro e he
    -- e ∈ edgeFinset: fiber = {d₀, d₀.symm}
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      set d₀ : G.Dart := ⟨(u, v), hadj⟩
      rw [show Finset.univ.filter (fun d : G.Dart => d.edge = s(u, v)) =
        {d₀, d₀.symm} from by
          ext d'; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton]
          exact SimpleGraph.dart_edge_eq_iff d' d₀]
      rw [Finset.sum_insert (show d₀ ∉ ({d₀.symm} : Finset _) from by
        simp only [Finset.mem_singleton]; exact d₀.symm_ne.symm),
        Finset.sum_singleton]
      simp only [Sym2.lift_mk, d₀, SimpleGraph.Dart.symm, Prod.swap]
  rw [hdart_edge, hdart_vertex]

/-- **Sub-lemma 4**: Degree bound — edge sum ≤ 2Δ · vertex sum.
Uses `(a-b)² ≤ 2(a²+b²)` and each vertex in ≤ Δ edges. -/
lemma edge_degree_bound (f : V → ℝ) :
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (f u - f v) ^ 2,
        fun u v => by ring⟩ e ≤
      2 * ↑G.maxDegree * ∑ v : V, f v ^ 2 := by
  -- Step 1: (a-b)² ≤ 2(a²+b²) for each edge
  have hineq : ∀ a b : ℝ, (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    intro a b; nlinarith [sq_nonneg (a + b)]
  -- Step 2: bound each Sym2.lift term
  calc ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e
    _ ≤ ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => 2 * (f u ^ 2 + f v ^ 2), fun u v => by ring⟩ e := by
        apply Finset.sum_le_sum; intro e he
        induction e using Sym2.ind with | _ u v => exact hineq (f u) (f v)
    -- Step 3: expand edge sum → vertex-degree-weighted sum
    -- Each vertex v contributes f v² once per incident edge = degree v times
    -- ∑_E 2(f u² + f v²) = 2 ∑_v degree(v) · f v²
    _ ≤ 2 * ↑G.maxDegree * ∑ v : V, f v ^ 2 := by
        -- Factor 2 out, use weighted_edge_vertex_sum, then degree ≤ maxDegree
        calc ∑ e ∈ G.edgeFinset,
            Sym2.lift ⟨fun u v => 2 * (f u ^ 2 + f v ^ 2), fun u v => by ring⟩ e
          _ = 2 * ∑ v : V, ↑(G.degree v) * f v ^ 2 := by
              rw [show ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v =>
                  2 * (f u ^ 2 + f v ^ 2), fun u v => by ring⟩ e =
                2 * ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v =>
                  f u ^ 2 + f v ^ 2, fun u v => by ring⟩ e from by
                    rw [Finset.mul_sum]; congr 1; ext e
                    induction e using Sym2.ind with | _ u v =>
                      simp only [Sym2.lift_mk]]
              rw [weighted_edge_vertex_sum]
          _ ≤ 2 * (↑G.maxDegree * ∑ v : V, f v ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum; intro v _
              exact mul_le_mul_of_nonneg_right
                (by exact_mod_cast G.degree_le_maxDegree v) (sq_nonneg _)
          _ = 2 * ↑G.maxDegree * ∑ v : V, f v ^ 2 := by ring

/-! ### Alon–Milman sign-flip helpers (for `sweep_pigeonhole`)

The classical proof of the hard direction of Cheeger's inequality reduces
the general Fiedler vector `f` to its positive part `f₊ := max f 0` by a
sign-flip (WLOG `|{f > 0}| ≤ n/2`), then applies the `h²` Cauchy–Schwarz +
pigeonhole argument on `f₊`. The following helpers encapsulate:

1. **`pos_or_neg_small`** — at least one of `{f > 0}`, `{f < 0}` has size ≤ n/2.
2. **`sq_sub_signsplit_le`** — pointwise `(a₊−b₊)² + (a₋−b₋)² ≤ (a−b)²`.
3. **`sq_sub_max_zero_le`** — pointwise `(max a 0 − max b 0)² ≤ (a − b)²`.
4. **`edge_sum_signsplit_le`** — Finset-level lift of (2) over edges.
5. **`edge_sum_max_zero_le`** — Finset-level lift of (3) over edges.

These are combined in `sweep_pigeonhole_aux` (the "small positive support" case),
with `sweep_pigeonhole` then reducing the general case via Case A / Case B on
the sign split. -/

/-- **Helper 1** (sign pigeonhole): at least one of the sign sets
`{v : f v > 0}` or `{v : f v < 0}` has cardinality `≤ n/2`.

Both exceeding would give a disjoint union of cardinality `> n`. -/
lemma pos_or_neg_small (f : V → ℝ) :
    (Finset.univ.filter fun w : V => (0:ℝ) < f w).card ≤ Fintype.card V / 2 ∨
    (Finset.univ.filter fun w : V => f w < 0).card ≤ Fintype.card V / 2 := by
  classical
  by_contra hboth
  push_neg at hboth
  obtain ⟨hpos, hneg⟩ := hboth
  have hdisj : Disjoint
      (Finset.univ.filter fun w : V => (0:ℝ) < f w)
      (Finset.univ.filter fun w : V => f w < 0) := by
    rw [Finset.disjoint_filter]
    intro w _ hw1 hw2; linarith
  have hcup : ((Finset.univ.filter fun w : V => (0:ℝ) < f w) ∪
               (Finset.univ.filter fun w : V => f w < 0)).card ≤
              Fintype.card V :=
    Finset.card_le_univ _
  rw [Finset.card_union_of_disjoint hdisj] at hcup
  omega

/-- **Helper 3** (pointwise sign-split inequality): the "doubling" identity
`(max a 0 − max b 0)² + (max (−a) 0 − max (−b) 0)² ≤ (a − b)²` on reals.

This is the key pointwise step for Laplacian monotonicity: the positive and
negative parts of `f` contribute edge-differences whose squares sum to ≤ the
original edge-difference squared. -/
lemma sq_sub_signsplit_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 + (max (-a) 0 - max (-b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · -- a ≥ 0, b ≥ 0: (a-b)² + 0² = (a-b)²
    rw [max_eq_left ha, max_eq_left hb,
        max_eq_right (neg_nonpos_of_nonneg ha), max_eq_right (neg_nonpos_of_nonneg hb)]
    nlinarith
  · -- a ≥ 0, b < 0: a² + b² ≤ (a-b)² = a² - 2ab + b² (use -2ab ≥ 0)
    rw [max_eq_left ha, max_eq_right hb.le,
        max_eq_right (neg_nonpos_of_nonneg ha), max_eq_left (neg_nonneg.mpr hb.le)]
    nlinarith [mul_nonneg ha (neg_nonneg.mpr hb.le)]
  · -- a < 0, b ≥ 0: symmetric
    rw [max_eq_right ha.le, max_eq_left hb,
        max_eq_left (neg_nonneg.mpr ha.le), max_eq_right (neg_nonpos_of_nonneg hb)]
    nlinarith [mul_nonneg (neg_nonneg.mpr ha.le) hb]
  · -- a < 0, b < 0: 0² + (-a-(-b))² = (a-b)²
    rw [max_eq_right ha.le, max_eq_right hb.le,
        max_eq_left (neg_nonneg.mpr ha.le), max_eq_left (neg_nonneg.mpr hb.le)]
    nlinarith

/-- **Helper 2** (positive-part 1-Lipschitz, squared): `(max a 0 − max b 0)² ≤ (a − b)²`.

Follows from `sq_sub_signsplit_le` by dropping the non-negative sign-down term. -/
lemma sq_sub_max_zero_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 ≤ (a - b) ^ 2 := by
  linarith [sq_sub_signsplit_le a b, sq_nonneg (max (-a) 0 - max (-b) 0)]

/-! ### Sweep / Cauchy–Schwarz helpers for `sweep_pigeonhole_aux`

The following six lemmas (Modal-verified individually) build the Alon–Milman
machinery for the hard direction of Cheeger. They are the formalized analogues
of Steps 1–6 of `informal/cheeger_sweep_pigeonhole.md`. The remaining
assembly (coarea for `h²`, the layer-cake norm identity, and the pigeonhole)
is still under construction in `sweep_pigeonhole_aux`. -/

/-- **Step 1** — sorting bijection: for any real weight `g : V → ℝ` there is an
equivalence `σ : Fin n ≃ V` listing the vertices in ascending `g`-order. This is
the `σ`/`hσ` pair that `discrete_coarea` consumes. -/
lemma exists_sort_equiv (g : V → ℝ) :
    ∃ σ : Fin (Fintype.card V) ≃ V,
      ∀ i j : Fin (Fintype.card V), i ≤ j → g (σ i) ≤ g (σ j) := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  refine ⟨(Tuple.sort (g ∘ e.symm)).trans e.symm, ?_⟩
  intro i j hij
  have hmono := Tuple.monotone_sort (g ∘ e.symm)
  have h := hmono hij
  simpa only [Equiv.trans_apply, Function.comp_apply] using h

/-- **Step 2** — positive-part level sets are small. With `h := max f 0`, any
upper level set `{w : t ≤ h w}` at threshold `t > 0` is contained in
`{w : 0 < f w}`, hence has cardinality `≤ n/2` under the small-positive-support
hypothesis. These are exactly the sweep cuts that must be `≤ n/2`. -/
lemma pos_part_level_small (f : V → ℝ) (t : ℝ) (ht : 0 < t)
    (hsmall : (Finset.univ.filter fun w : V => (0:ℝ) < f w).card ≤
        Fintype.card V / 2) :
    (Finset.univ.filter fun w : V => t ≤ max (f w) 0).card ≤
      Fintype.card V / 2 := by
  refine le_trans (Finset.card_le_card ?_) hsmall
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases le_or_gt (f w) 0 with h | h
  · rw [max_eq_right h] at hw; linarith
  · exact h

/-- **Step 3** — eigen chain: for a Fiedler vector (`L f = λ₂ f`),
`λ₂ · ‖f‖² = ∑_e (f_u − f_v)²` in this file's edge-sum form. Bridges the
matrix eigen-equation hypothesis to the combinatorial edge sum via
`quadratic_form_eq_edge_sum`. -/
lemma eigen_edge_chain (f : V → ℝ) (hV : Fintype.card V ≥ 2)
    (hfeig : (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f) :
    algebraicConnectivity G hV * (∑ v : V, f v ^ 2) =
      ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e := by
  have heig : dotProduct f ((G.lapMatrix ℝ).mulVec f) =
      algebraicConnectivity G hV * dotProduct f f := by
    rw [hfeig]; simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_comm (f _) (algebraicConnectivity G hV * f _),
      show ∀ x, algebraicConnectivity G hV * f x * f x
            = f x ^ 2 * algebraicConnectivity G hV from fun x => by ring]
    rw [← Finset.sum_mul]; ring
  have hlm : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f =
      dotProduct f ((G.lapMatrix ℝ).mulVec f) := by
    rw [Matrix.toLinearMap₂'_apply']
  have hqf := quadratic_form_eq_edge_sum G f
  rw [hlm, heig] at hqf
  have hdot : dotProduct f f = ∑ v, (f v) ^ 2 := by simp [dotProduct, sq]
  rw [hdot] at hqf
  exact hqf

/-- **Step 4** — positive-part Laplacian monotonicity (edge lift):
`∑_e (max f_u 0 − max f_v 0)² ≤ ∑_e (f_u − f_v)²`. Finset-level lift of the
pointwise `sq_sub_max_zero_le`. -/
lemma edge_sum_max_zero_le (f : V → ℝ) :
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (max (f u) 0 - max (f v) 0) ^ 2,
        fun u v => by ring⟩ e ≤
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e := by
  apply Finset.sum_le_sum
  intro e he
  induction e using Sym2.ind with
  | _ u v => exact sq_sub_max_zero_le (f u) (f v)

/-- **Step 5** — "sum" degree bound: `∑_e (h_u + h_v)² ≤ 2Δ · ‖h‖²`. Mirrors
`edge_degree_bound` (which is for the difference), via `(a+b)² ≤ 2(a²+b²)` and
`weighted_edge_vertex_sum`. Supplies the second Cauchy–Schwarz factor. -/
lemma edge_sum_add_sq_degree_bound (h : V → ℝ) :
    ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (h u + h v) ^ 2, fun u v => by ring⟩ e ≤
      2 * ↑G.maxDegree * ∑ v : V, h v ^ 2 := by
  have hineq : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    intro a b; nlinarith [sq_nonneg (a - b)]
  calc ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (h u + h v) ^ 2, fun u v => by ring⟩ e
    _ ≤ ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => 2 * (h u ^ 2 + h v ^ 2), fun u v => by ring⟩ e := by
        apply Finset.sum_le_sum; intro e he
        induction e using Sym2.ind with | _ u v => exact hineq (h u) (h v)
    _ ≤ 2 * ↑G.maxDegree * ∑ v : V, h v ^ 2 := by
        calc ∑ e ∈ G.edgeFinset,
            Sym2.lift ⟨fun u v => 2 * (h u ^ 2 + h v ^ 2), fun u v => by ring⟩ e
          _ = 2 * ∑ v : V, ↑(G.degree v) * h v ^ 2 := by
              rw [show ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v =>
                  2 * (h u ^ 2 + h v ^ 2), fun u v => by ring⟩ e =
                2 * ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v =>
                  h u ^ 2 + h v ^ 2, fun u v => by ring⟩ e from by
                    rw [Finset.mul_sum]; congr 1; ext e
                    induction e using Sym2.ind with | _ u v =>
                      simp only [Sym2.lift_mk]]
              rw [weighted_edge_vertex_sum]
          _ ≤ 2 * (↑G.maxDegree * ∑ v : V, h v ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum; intro v _
              exact mul_le_mul_of_nonneg_right
                (by exact_mod_cast G.degree_le_maxDegree v) (sq_nonneg _)
          _ = 2 * ↑G.maxDegree * ∑ v : V, h v ^ 2 := by ring

/-- **Step 6** — edge Cauchy–Schwarz for the squared function (`h ≥ 0`):
`(∑_e |h_u² − h_v²|)² ≤ (∑_e (h_u − h_v)²) · (∑_e (h_u + h_v)²)`.
Uses `|h_u² − h_v²| = |h_u − h_v|·(h_u + h_v)` then discrete Cauchy–Schwarz. -/
lemma edge_sqdiff_cauchy_schwarz (h : V → ℝ) (hnn : ∀ v, 0 ≤ h v) :
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => |h u ^ 2 - h v ^ 2|,
          fun u v => by simp only [abs_sub_comm]⟩ e) ^ 2 ≤
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (h u - h v) ^ 2, fun u v => by ring⟩ e) *
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (h u + h v) ^ 2, fun u v => by ring⟩ e) := by
  -- `let` (not `set`) so the Sym2.lift applications stay defeq-reducible.
  let F : Sym2 V → ℝ :=
    Sym2.lift ⟨fun u v => |h u - h v|, fun u v => by simp only [abs_sub_comm]⟩
  let Gg : Sym2 V → ℝ :=
    Sym2.lift ⟨fun u v => h u + h v, fun u v => by ring⟩
  have key := Finset.sum_mul_sq_le_sq_mul_sq G.edgeFinset F Gg
  have e1 : ∑ e ∈ G.edgeFinset, F e * Gg e =
      ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => |h u ^ 2 - h v ^ 2|,
          fun u v => by simp only [abs_sub_comm]⟩ e := by
    apply Finset.sum_congr rfl; intro e _
    induction e using Sym2.ind with
    | _ u v =>
      show |h u - h v| * (h u + h v) = |h u ^ 2 - h v ^ 2|
      rw [show h u ^ 2 - h v ^ 2 = (h u - h v) * (h u + h v) by ring, abs_mul,
          abs_of_nonneg (by linarith [hnn u, hnn v] : (0:ℝ) ≤ h u + h v)]
  have e2 : ∑ e ∈ G.edgeFinset, F e ^ 2 =
      ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (h u - h v) ^ 2, fun u v => by ring⟩ e := by
    apply Finset.sum_congr rfl; intro e _
    induction e using Sym2.ind with
    | _ u v => show |h u - h v| ^ 2 = (h u - h v) ^ 2; rw [sq_abs]
  have e3 : ∑ e ∈ G.edgeFinset, Gg e ^ 2 =
      ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (h u + h v) ^ 2, fun u v => by ring⟩ e := by
    apply Finset.sum_congr rfl; intro e _
    induction e using Sym2.ind with
    | _ u v => rfl
  calc (∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => |h u ^ 2 - h v ^ 2|,
            fun u v => by simp only [abs_sub_comm]⟩ e) ^ 2
      = (∑ e ∈ G.edgeFinset, F e * Gg e) ^ 2 := by rw [e1]
    _ ≤ (∑ e ∈ G.edgeFinset, F e ^ 2) * (∑ e ∈ G.edgeFinset, Gg e ^ 2) := key
    _ = _ := by rw [e2, e3]

/-- **Step 7a** — squaring preserves the sort order for non-negative `h`: if `σ`
lists `h` ascending and `h ≥ 0`, then `σ` also lists `h²` ascending. This is the
prerequisite that lets `discrete_coarea` be applied to `h²`. -/
lemma sq_sorted_of_nonneg (h : V → ℝ) (hnn : ∀ v, 0 ≤ h v)
    (σ : Fin (Fintype.card V) ≃ V)
    (hσ : ∀ i j, i ≤ j → h (σ i) ≤ h (σ j)) :
    ∀ i j : Fin (Fintype.card V), i ≤ j → (h (σ i)) ^ 2 ≤ (h (σ j)) ^ 2 := by
  intro i j hij
  rw [pow_two, pow_two]
  exact mul_self_le_mul_self (hnn (σ i)) (hσ i j hij)

/-- **Step 7b** — discrete coarea formula for `h²`: applies `discrete_coarea` to
the non-negative function `h²` using `h`'s own sort `σ`. The level cuts are
`{w : (h w)² ≥ (h (σ_{k+1}))²}`. -/
lemma coarea_sq (h : V → ℝ) (hnn : ∀ v, 0 ≤ h v)
    (σ : Fin (Fintype.card V) ≃ V)
    (hσ : ∀ i j, i ≤ j → h (σ i) ≤ h (σ j))
    (hV : Fintype.card V ≥ 2) :
    ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => |(h u) ^ 2 - (h v) ^ 2|,
          fun u v => by simp only [abs_sub_comm]⟩ e =
      ∑ k : Fin (Fintype.card V - 1),
        ((h (σ ⟨k.val + 1, by omega⟩)) ^ 2 - (h (σ ⟨k.val, by omega⟩)) ^ 2) *
        ((edgeBoundary G (Finset.univ.filter fun w =>
          (h w) ^ 2 ≥ (h (σ ⟨k.val + 1, by omega⟩)) ^ 2)).card : ℝ) := by
  exact discrete_coarea G (fun v => (h v) ^ 2) σ
    (sq_sorted_of_nonneg h hnn σ hσ) hV

/-- **Step 8** — discrete layer-cake (co-area for the vertex sum): for a sorted
weight `g` (`σ` lists `g` ascending),
`∑_v g v = N·g(σ₀) + ∑_k (g(σ_{k+1}) − g(σ_k))·|{w : g w ≥ g(σ_{k+1})}|`.
Proved by double counting: write each `|T_k|` as `∑_w [g(σ_{k+1}) ≤ g w]`, swap
the sums, and telescope per vertex (the index/value indicators agree because the
gap vanishes on ties). -/
lemma layer_cake_sum (g : V → ℝ) (σ : Fin (Fintype.card V) ≃ V)
    (hσ : ∀ i j, i ≤ j → g (σ i) ≤ g (σ j)) (hV : Fintype.card V ≥ 2) :
    ∑ v : V, g v =
      (Fintype.card V : ℝ) * g (σ ⟨0, by omega⟩) +
      ∑ k : Fin (Fintype.card V - 1),
        (g (σ ⟨k.val + 1, by omega⟩) - g (σ ⟨k.val, by omega⟩)) *
        ((Finset.univ.filter fun w => g w ≥ g (σ ⟨k.val + 1, by omega⟩)).card : ℝ) := by
  classical
  set s : ℕ → ℝ := fun k => if hk : k < Fintype.card V then g (σ ⟨k, hk⟩) else 0
    with hs_def
  have hsk : ∀ (k : ℕ) (hk : k < Fintype.card V), s k = g (σ ⟨k, hk⟩) := by
    intro k hk; simp only [hs_def, dif_pos hk]
  -- (1) card → indicator sum
  have hcard : ∀ k : Fin (Fintype.card V - 1),
      ((Finset.univ.filter fun w => g w ≥ g (σ ⟨k.val + 1, by omega⟩)).card : ℝ)
      = ∑ w : V, (if g (σ ⟨k.val + 1, by omega⟩) ≤ g w then (1:ℝ) else 0) := by
    intro k
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl; intro w _
    simp only [ge_iff_le, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  -- (2) per-vertex telescoping identity
  have hper : ∀ w : V,
      ∑ k : Fin (Fintype.card V - 1),
        (g (σ ⟨k.val + 1, by omega⟩) - g (σ ⟨k.val, by omega⟩)) *
          (if g (σ ⟨k.val + 1, by omega⟩) ≤ g w then (1:ℝ) else 0)
        = g w - g (σ ⟨0, by omega⟩) := by
    intro w
    have hjw_lt : (σ.symm w).val < Fintype.card V := (σ.symm w).isLt
    set jw := (σ.symm w).val with hjw
    have hgw : g w = g (σ ⟨jw, hjw_lt⟩) := by
      have hfin : (⟨jw, hjw_lt⟩ : Fin (Fintype.card V)) = σ.symm w := by apply Fin.ext; rfl
      rw [hfin, Equiv.apply_symm_apply]
    rw [hgw]
    have hterm : ∀ k : Fin (Fintype.card V - 1),
        (g (σ ⟨k.val + 1, by omega⟩) - g (σ ⟨k.val, by omega⟩)) *
          (if g (σ ⟨k.val + 1, by omega⟩) ≤ g (σ ⟨jw, hjw_lt⟩) then (1:ℝ) else 0)
        = (g (σ ⟨k.val + 1, by omega⟩) - g (σ ⟨k.val, by omega⟩)) *
          (if k.val + 1 ≤ jw then (1:ℝ) else 0) := by
      intro k
      by_cases hidx : k.val + 1 ≤ jw
      · have hle : g (σ ⟨k.val + 1, by omega⟩) ≤ g (σ ⟨jw, hjw_lt⟩) :=
          hσ ⟨k.val + 1, by omega⟩ ⟨jw, hjw_lt⟩ (Fin.mk_le_mk.mpr (by omega))
        rw [if_pos hidx, if_pos hle]
      · push_neg at hidx
        by_cases hval : g (σ ⟨k.val + 1, by omega⟩) ≤ g (σ ⟨jw, hjw_lt⟩)
        · have hk_ge : g (σ ⟨jw, hjw_lt⟩) ≤ g (σ ⟨k.val, by omega⟩) :=
            hσ ⟨jw, hjw_lt⟩ ⟨k.val, by omega⟩ (Fin.mk_le_mk.mpr (by omega))
          have hk_le : g (σ ⟨k.val, by omega⟩) ≤ g (σ ⟨k.val + 1, by omega⟩) :=
            hσ ⟨k.val, by omega⟩ ⟨k.val + 1, by omega⟩ (Fin.mk_le_mk.mpr (by omega))
          have hgap0 : g (σ ⟨k.val + 1, by omega⟩) - g (σ ⟨k.val, by omega⟩) = 0 := by
            linarith
          rw [hgap0]; ring
        · rw [if_neg hval, if_neg (show ¬ k.val + 1 ≤ jw by omega)]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [Finset.sum_congr rfl (fun (k : Fin (Fintype.card V - 1)) _ =>
      show (g (σ ⟨k.val + 1, by omega⟩) - g (σ ⟨k.val, by omega⟩)) *
            (if k.val + 1 ≤ jw then (1:ℝ) else 0)
         = (s (k.val + 1) - s k.val) * (if k.val + 1 ≤ jw then (1:ℝ) else 0)
      from by rw [hsk (k.val + 1) (by omega), hsk k.val (by omega)])]
    rw [Fin.sum_univ_eq_sum_range
      (fun m => (s (m + 1) - s m) * (if m + 1 ≤ jw then (1:ℝ) else 0)) (Fintype.card V - 1)]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : (Finset.range (Fintype.card V - 1)).filter (fun m => m + 1 ≤ jw)
        = Finset.range jw := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilter, Finset.sum_range_sub s jw, hsk jw hjw_lt, hsk 0 (by omega)]
  -- (3) assemble
  have key :
      ∑ k : Fin (Fintype.card V - 1),
        (g (σ ⟨k.val + 1, by omega⟩) - g (σ ⟨k.val, by omega⟩)) *
        ((Finset.univ.filter fun w => g w ≥ g (σ ⟨k.val + 1, by omega⟩)).card : ℝ)
      = (∑ v : V, g v) - (Fintype.card V : ℝ) * g (σ ⟨0, by omega⟩) := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [hcard k])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun w _ => hper w)]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  linarith [key]

/-- **Step 9a (pointwise)** — `(max a 0)² + (max (−a) 0)² = a²`. -/
lemma sq_max_sq_neg_max (a : ℝ) : (max a 0) ^ 2 + (max (-a) 0) ^ 2 = a ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · rw [max_eq_left ha, max_eq_right (neg_nonpos_of_nonneg ha)]; ring
  · rw [max_eq_right ha.le, max_eq_left (neg_nonneg.mpr ha.le)]; ring

/-- **Step 9a (vertex sum)** — the positive and negative parts split the norm:
`‖f₊‖² + ‖f₋‖² = ‖f‖²`. -/
lemma norm_pos_neg_split (f : V → ℝ) :
    (∑ v : V, (max (f v) 0) ^ 2) + (∑ v : V, (max (-(f v)) 0) ^ 2)
      = ∑ v : V, (f v) ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro v _
  exact sq_max_sq_neg_max (f v)

/-- **Step 9b** — doubled Laplacian monotonicity (edge lift of `sq_sub_signsplit_le`):
`∑_e (f₊_u − f₊_v)² + ∑_e (f₋_u − f₋_v)² ≤ ∑_e (f_u − f_v)²`. -/
lemma edge_signsplit_le (f : V → ℝ) :
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (f u) 0 - max (f v) 0) ^ 2,
          fun u v => by ring⟩ e)
    + (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (-(f u)) 0 - max (-(f v)) 0) ^ 2,
          fun u v => by ring⟩ e)
    ≤ ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro e he
  induction e using Sym2.ind with
  | _ u v => exact sq_sub_signsplit_le (f u) (f v)

/-- **Bilinear edge identity** (polarization of `quadratic_form_eq_edge_sum`):
`∑_e (x_u − x_v)(y_u − y_v) = xᵀ L y`. -/
lemma bilinear_edge_sum (x y : V → ℝ) :
    ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (x u - x v) * (y u - y v), fun u v => by ring⟩ e
      = dotProduct x ((G.lapMatrix ℝ).mulVec y) := by
  have happ : ∀ a b : V → ℝ,
      Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) a b = dotProduct a ((G.lapMatrix ℝ).mulVec b) := by
    intro a b; rw [Matrix.toLinearMap₂'_apply']
  have hsym : dotProduct y ((G.lapMatrix ℝ).mulVec x)
      = dotProduct x ((G.lapMatrix ℝ).mulVec y) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        show (G.lapMatrix ℝ).transpose = G.lapMatrix ℝ from G.isSymm_lapMatrix (R := ℝ)]
    exact dotProduct_comm _ _
  have hpolar : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) (x + y) (x + y)
      = dotProduct x ((G.lapMatrix ℝ).mulVec x)
        + 2 * dotProduct x ((G.lapMatrix ℝ).mulVec y)
        + dotProduct y ((G.lapMatrix ℝ).mulVec y) := by
    simp only [map_add, LinearMap.add_apply, happ]
    rw [hsym]; ring
  have hedge :
      (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => ((x + y) u - (x + y) v) ^ 2, fun u v => by ring⟩ e)
      = (∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => (x u - x v) ^ 2, fun u v => by ring⟩ e)
        + 2 * (∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => (x u - x v) * (y u - y v), fun u v => by ring⟩ e)
        + (∑ e ∈ G.edgeFinset,
          Sym2.lift ⟨fun u v => (y u - y v) ^ 2, fun u v => by ring⟩ e) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _
    induction e using Sym2.ind with
    | _ u v => simp only [Sym2.lift_mk, Pi.add_apply]; ring
  have hx : dotProduct x ((G.lapMatrix ℝ).mulVec x)
      = ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => (x u - x v) ^ 2, fun u v => by ring⟩ e :=
    (happ x x).symm.trans (quadratic_form_eq_edge_sum G x)
  have hy : dotProduct y ((G.lapMatrix ℝ).mulVec y)
      = ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => (y u - y v) ^ 2, fun u v => by ring⟩ e :=
    (happ y y).symm.trans (quadratic_form_eq_edge_sum G y)
  have qfxy := quadratic_form_eq_edge_sum G (x + y)
  linarith [hpolar, hedge, hx, hy, qfxy]

/-- Pointwise truncation inequality: `(f₊_u − f₊_v)² ≤ (f₊_u − f₊_v)(f_u − f_v)`. -/
lemma sq_sub_max_le_mul (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 ≤ (max a 0 - max b 0) * (a - b) := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [max_eq_left ha, max_eq_left hb]; nlinarith
  · rw [max_eq_left ha, max_eq_right hb.le]
    nlinarith [mul_nonneg ha (neg_nonneg.mpr hb.le)]
  · rw [max_eq_right ha.le, max_eq_left hb]
    nlinarith [mul_nonneg (neg_nonneg.mpr ha.le) hb]
  · rw [max_eq_right ha.le, max_eq_right hb.le]; nlinarith

/-- `⟨f₊, f⟩ = ‖f₊‖²` pointwise: `max (f v) 0 · f v = (max (f v) 0)²`. -/
lemma dot_h_f (f : V → ℝ) :
    dotProduct (fun v => max (f v) 0) f = ∑ v : V, (max (f v) 0) ^ 2 := by
  show ∑ v : V, (max (f v) 0) * f v = ∑ v : V, (max (f v) 0) ^ 2
  apply Finset.sum_congr rfl; intro v _
  rcases le_or_gt 0 (f v) with h | h
  · rw [max_eq_left h]; ring
  · rw [max_eq_right h.le]; ring

/-- **Truncation preserves the Rayleigh quotient** (Trevisan / Houdré–Tetali):
for a Fiedler vector (`L f = λ₂ f`) and `h = max f 0`,
`∑_e (h_u − h_v)² ≤ λ₂ · ‖h‖²`. The key fact eliminating the `‖f‖/‖h‖` factor;
all `h`-sweep cuts then lie in `{f > 0}` (size ≤ n/2), so no doubling is needed. -/
lemma rayleigh_truncation_le (f : V → ℝ) (hV : Fintype.card V ≥ 2)
    (hfeig : (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f) :
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (f u) 0 - max (f v) 0) ^ 2, fun u v => by ring⟩ e)
      ≤ algebraicConnectivity G hV * ∑ v : V, (max (f v) 0) ^ 2 := by
  have hstep1 :
      (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (f u) 0 - max (f v) 0) ^ 2, fun u v => by ring⟩ e)
      ≤ ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (f u) 0 - max (f v) 0) * (f u - f v),
          fun u v => by ring⟩ e := by
    apply Finset.sum_le_sum; intro e he
    induction e using Sym2.ind with
    | _ u v => exact sq_sub_max_le_mul (f u) (f v)
  have hconv :
      (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (f u) 0 - max (f v) 0) * (f u - f v),
          fun u v => by ring⟩ e)
      = ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v =>
          ((fun w => max (f w) 0) u - (fun w => max (f w) 0) v) * (f u - f v),
          fun u v => by ring⟩ e := by
    apply Finset.sum_congr rfl; intro e _
    induction e using Sym2.ind with | _ u v => rfl
  have hstep2 :
      (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (max (f u) 0 - max (f v) 0) * (f u - f v),
          fun u v => by ring⟩ e)
      = algebraicConnectivity G hV * ∑ v : V, (max (f v) 0) ^ 2 := by
    rw [hconv, bilinear_edge_sum G (fun w => max (f w) 0) f, hfeig,
        dotProduct_smul, smul_eq_mul, dot_h_f]
  linarith [hstep1, hstep2]

/-- Numerator bound: `∑_e |h_u² − h_v²| ≤ √(2λ₂Δ)·‖h‖²` for `h = max f 0`.
Cauchy–Schwarz, then `rayleigh_truncation_le` and `edge_sum_add_sq_degree_bound`,
then `Real.sqrt` algebra. -/
lemma sweep_numerator_bound (f : V → ℝ) (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (hfeig : (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f) :
    (∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => |(max (f u) 0) ^ 2 - (max (f v) 0) ^ 2|,
          fun u v => by simp only [abs_sub_comm]⟩ e)
      ≤ Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree)
          * ∑ v : V, (max (f v) 0) ^ 2 := by
  have hnn : ∀ v, 0 ≤ max (f v) 0 := fun v => le_max_right _ _
  have hHnn : 0 ≤ ∑ v : V, (max (f v) 0) ^ 2 := Finset.sum_nonneg (fun v _ => sq_nonneg _)
  have hac : 0 ≤ algebraicConnectivity G hV := (algebraicConnectivity_pos G hconn hV).le
  have hΔ : 0 ≤ (G.maxDegree : ℝ) := Nat.cast_nonneg _
  have hcs := edge_sqdiff_cauchy_schwarz G (fun v => max (f v) 0) hnn
  have hSb := edge_sum_add_sq_degree_bound G (fun v => max (f v) 0)
  simp only [] at hcs hSb
  have hD := rayleigh_truncation_le G f hV hfeig
  set N := ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => |(max (f u) 0) ^ 2 - (max (f v) 0) ^ 2|,
        fun u v => by simp only [abs_sub_comm]⟩ e with hNdef
  set Ds := ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (max (f u) 0 - max (f v) 0) ^ 2, fun u v => by ring⟩ e with hDdef
  set Ss := ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => (max (f u) 0 + max (f v) 0) ^ 2, fun u v => by ring⟩ e with hSdef
  set H := ∑ v : V, (max (f v) 0) ^ 2 with hHdef
  have hNnn : 0 ≤ N := by
    rw [hNdef]; apply Finset.sum_nonneg; intro e he
    induction e using Sym2.ind with | _ u v => exact abs_nonneg _
  have hSsnn : 0 ≤ Ss := by
    rw [hSdef]; apply Finset.sum_nonneg; intro e he
    induction e using Sym2.ind with | _ u v => exact sq_nonneg _
  have hN2 : N ^ 2 ≤ (2 * algebraicConnectivity G hV * ↑G.maxDegree) * H ^ 2 := by
    calc N ^ 2 ≤ Ds * Ss := hcs
      _ ≤ (algebraicConnectivity G hV * H) * (2 * ↑G.maxDegree * H) :=
          mul_le_mul hD hSb hSsnn (mul_nonneg hac hHnn)
      _ = (2 * algebraicConnectivity G hV * ↑G.maxDegree) * H ^ 2 := by ring
  calc N = Real.sqrt (N ^ 2) := (Real.sqrt_sq hNnn).symm
    _ ≤ Real.sqrt ((2 * algebraicConnectivity G hV * ↑G.maxDegree) * H ^ 2) :=
        Real.sqrt_le_sqrt hN2
    _ = Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) * H := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hHnn]

/-- Weighted pigeonhole: if `∑ gᵢdᵢ ≤ c·∑ gᵢtᵢ` with non-negative weights `g`
and some positive weight, then some index with positive weight has `dᵢ ≤ c·tᵢ`. -/
lemma exists_pos_ratio {ι : Type*} (s : Finset ι) (g d t : ι → ℝ) (c : ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i)
    (hpos : ∃ i ∈ s, 0 < g i)
    (hsum : ∑ i ∈ s, g i * d i ≤ c * ∑ i ∈ s, g i * t i) :
    ∃ i ∈ s, 0 < g i ∧ d i ≤ c * t i := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ i ∈ s, g i * (c * t i) < ∑ i ∈ s, g i * d i := by
    apply Finset.sum_lt_sum
    · intro i hi
      rcases (hg i hi).lt_or_eq with h0 | h0
      · have := hcon i hi h0; nlinarith
      · rw [← h0]; simp
    · obtain ⟨i, hi, hgi⟩ := hpos
      exact ⟨i, hi, by have := hcon i hi hgi; nlinarith⟩
  have heq : ∑ i ∈ s, g i * (c * t i) = c * ∑ i ∈ s, g i * t i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [heq] at hlt
  linarith

lemma sweep_pigeonhole_aux
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (f : V → ℝ) (hf : f ≠ 0) (hfsum : ∑ v : V, f v = 0)
    (hfeig : (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f)
    (hposSmall : (Finset.univ.filter fun w : V => (0:ℝ) < f w).card ≤
        Fintype.card V / 2) :
    ∃ (S : Finset V), S.Nonempty ∧ Sᶜ.Nonempty ∧
      S.card ≤ Fintype.card V / 2 ∧
      ((edgeBoundary G S).card : ℝ) / ↑S.card ≤
        Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) := by
  classical
  have hnn : ∀ v, (0:ℝ) ≤ max (f v) 0 := fun v => le_max_right _ _
  obtain ⟨σ, hσ⟩ := exists_sort_equiv (fun v => max (f v) 0)
  have hσsq : ∀ i j : Fin (Fintype.card V), i ≤ j →
      (max (f (σ i)) 0) ^ 2 ≤ (max (f (σ j)) 0) ^ 2 :=
    sq_sorted_of_nonneg (fun v => max (f v) 0) hnn σ hσ
  have hex_nonpos : ∃ w, f w ≤ 0 := by
    by_contra hc; push_neg at hc
    have huniv : (Finset.univ.filter fun w : V => (0:ℝ) < f w) = Finset.univ := by
      ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact hc w
    rw [huniv, Finset.card_univ] at hposSmall; omega
  have hmin0 : max (f (σ ⟨0, by omega⟩)) 0 = 0 := by
    obtain ⟨w, hw⟩ := hex_nonpos
    have hle : max (f (σ ⟨0, by omega⟩)) 0 ≤ max (f w) 0 := by
      have := hσ ⟨0, by omega⟩ (σ.symm w) (Fin.le_def.mpr (Nat.zero_le _))
      rwa [Equiv.apply_symm_apply] at this
    have hw0 : max (f w) 0 = 0 := max_eq_right hw
    linarith [hnn (σ ⟨0, by omega⟩)]
  have hmin0sq : (max (f (σ ⟨0, by omega⟩)) 0) ^ 2 = 0 := by rw [hmin0]; ring
  have hex_pos : ∃ v, 0 < f v := by
    by_contra hc; push_neg at hc
    exact hf (funext fun v =>
      (Finset.sum_eq_zero_iff_of_nonpos (fun w _ => hc w)).mp hfsum v (Finset.mem_univ v))
  have hHpos : 0 < ∑ v : V, (max (f v) 0) ^ 2 := by
    obtain ⟨v, hv⟩ := hex_pos
    refine Finset.sum_pos' (fun w _ => sq_nonneg _) ⟨v, Finset.mem_univ v, ?_⟩
    have : 0 < max (f v) 0 := lt_max_of_lt_left hv
    positivity
  have hcoarea := coarea_sq G (fun v => max (f v) 0) hnn σ hσ hV
  have hlayer := layer_cake_sum (fun v => (max (f v) 0) ^ 2) σ hσsq hV
  have hnum := sweep_numerator_bound G f hconn hV hfeig
  set gap : Fin (Fintype.card V - 1) → ℝ :=
    fun k => (max (f (σ ⟨k.val + 1, by omega⟩)) 0) ^ 2
              - (max (f (σ ⟨k.val, by omega⟩)) 0) ^ 2 with hgap
  set Tset : Fin (Fintype.card V - 1) → Finset V :=
    fun k => Finset.univ.filter fun w =>
      (max (f w) 0) ^ 2 ≥ (max (f (σ ⟨k.val + 1, by omega⟩)) 0) ^ 2 with hTset
  have hHeq : ∑ v : V, (max (f v) 0) ^ 2 = ∑ k, gap k * ((Tset k).card : ℝ) := by
    rw [hlayer, hmin0sq]; ring
  have hmaster : ∑ k, gap k * ((edgeBoundary G (Tset k)).card : ℝ)
      ≤ Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree)
          * ∑ k, gap k * ((Tset k).card : ℝ) := by
    calc ∑ k, gap k * ((edgeBoundary G (Tset k)).card : ℝ)
        = ∑ e ∈ G.edgeFinset,
            Sym2.lift ⟨fun u v => |(max (f u) 0) ^ 2 - (max (f v) 0) ^ 2|,
              fun u v => by simp only [abs_sub_comm]⟩ e := hcoarea.symm
      _ ≤ Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree)
            * ∑ v : V, (max (f v) 0) ^ 2 := hnum
      _ = Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree)
            * ∑ k, gap k * ((Tset k).card : ℝ) := by rw [hHeq]
  have hgap_nn : ∀ k ∈ (Finset.univ : Finset (Fin (Fintype.card V - 1))), 0 ≤ gap k := by
    intro k _; rw [hgap]
    exact sub_nonneg.mpr (hσsq ⟨k.val, by omega⟩ ⟨k.val + 1, by omega⟩
      (Fin.mk_le_mk.mpr (by omega)))
  have hgap_pos : ∃ k ∈ (Finset.univ : Finset (Fin (Fintype.card V - 1))), 0 < gap k := by
    by_contra hc; push_neg at hc
    have : ∑ k, gap k * ((Tset k).card : ℝ) = 0 := by
      apply Finset.sum_eq_zero; intro k hk
      have hz := le_antisymm (hc k hk) (hgap_nn k hk); rw [hz, zero_mul]
    rw [← hHeq] at this; exact absurd this (ne_of_gt hHpos)
  obtain ⟨k, -, hkpos, hkratio⟩ := exists_pos_ratio Finset.univ gap
    (fun k => ((edgeBoundary G (Tset k)).card : ℝ)) (fun k => ((Tset k).card : ℝ))
    (Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree)) hgap_nn hgap_pos hmaster
  have hkp1pos : 0 < max (f (σ ⟨k.val + 1, by omega⟩)) 0 := by
    have h2 : 0 < (max (f (σ ⟨k.val + 1, by omega⟩)) 0) ^ 2 := by
      have := hkpos; rw [hgap] at this
      nlinarith [sq_nonneg (max (f (σ ⟨k.val, by omega⟩)) 0)]
    nlinarith [hnn (σ ⟨k.val + 1, by omega⟩)]
  have hmem : σ ⟨k.val + 1, by omega⟩ ∈ Tset k := by
    rw [hTset]; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ge_iff_le, le_refl]
  have hSne : (Tset k).Nonempty := ⟨_, hmem⟩
  have hScard_pos : 0 < (Tset k).card := Finset.card_pos.mpr hSne
  refine ⟨Tset k, hSne, ?_, ?_, ?_⟩
  · refine ⟨σ ⟨0, by omega⟩, ?_⟩
    rw [Finset.mem_compl, hTset]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ge_iff_le, not_le, hmin0sq]
    positivity
  · refine le_trans (Finset.card_le_card ?_)
      (pos_part_level_small f (max (f (σ ⟨k.val + 1, by omega⟩)) 0) hkp1pos hposSmall)
    intro w hw
    rw [hTset, Finset.mem_filter] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have ha := hnn (σ ⟨k.val + 1, by omega⟩); have hb := hnn w
    rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb]
    exact Real.sqrt_le_sqrt hw.2
  · rw [div_le_iff₀ (by exact_mod_cast hScard_pos)]
    exact hkratio

/-- **Sub-lemma 5**: Pigeonhole — ∃ good threshold. -/
lemma sweep_pigeonhole
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (f : V → ℝ) (hf : f ≠ 0) (hfsum : ∑ v : V, f v = 0)
    (hfeig : (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f) :
    ∃ (S : Finset V), S.Nonempty ∧ Sᶜ.Nonempty ∧
      S.card ≤ Fintype.card V / 2 ∧
      ((edgeBoundary G S).card : ℝ) / ↑S.card ≤
        Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) := by
  -- **Sign reduction** (`pos_or_neg_small`): WLOG the positive support is small.
  -- In Case A we apply `sweep_pigeonhole_aux` directly; in Case B we apply it
  -- to `-f`, whose positive support `{(-f) > 0} = {f < 0}` is the small side,
  -- and whose Laplacian eigen-equation and sum-zero property are preserved
  -- under negation. The auxiliary lemma returns a generic `S : Finset V`, so
  -- no translation back to the `S_k` form is needed.
  rcases pos_or_neg_small f with hposSmall | hnegSmall
  · -- Case A: |{f > 0}| ≤ n/2
    exact sweep_pigeonhole_aux G hconn hV f hf hfsum hfeig hposSmall
  · -- Case B: |{f < 0}| ≤ n/2 — reduce to Case A via `-f`.
    have hf' : (-f) ≠ 0 := by
      intro hneg
      apply hf
      funext v
      have := congrFun hneg v
      simp only [Pi.neg_apply, Pi.zero_apply, neg_eq_zero] at this
      exact this
    have hfsum' : ∑ v : V, (-f) v = 0 := by
      simp only [Pi.neg_apply, Finset.sum_neg_distrib, hfsum, neg_zero]
    have hfeig' : (G.lapMatrix ℝ).mulVec (-f) =
        algebraicConnectivity G hV • (-f) := by
      rw [Matrix.mulVec_neg, hfeig, ← smul_neg]
    have hposSmall' :
        (Finset.univ.filter fun w : V => (0:ℝ) < (-f) w).card ≤
          Fintype.card V / 2 := by
      refine le_trans (le_of_eq ?_) hnegSmall
      congr 1
      ext w
      simp [Pi.neg_apply, neg_pos]
    exact sweep_pigeonhole_aux G hconn hV (-f) hf' hfsum' hfeig' hposSmall'

/-- Sweep cut bound: ∃ threshold with expansion ≤ √(2λ₂Δ).
Follows from `sweep_pigeonhole`. -/
lemma sweep_cut_bound
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (f : V → ℝ) (hf : f ≠ 0) (hfsum : ∑ v : V, f v = 0)
    (hfeig : (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f) :
    ∃ (S : Finset V), S.Nonempty ∧ Sᶜ.Nonempty ∧
      S.card ≤ Fintype.card V / 2 ∧
      (edgeBoundary G S).card / (S.card : ℝ) ≤
        Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) := by
  exact sweep_pigeonhole G hconn hV f hf hfsum hfeig

/-- **Cheeger inequality** (Alon–Milman): `h(G)²/(2Δ) ≤ λ₂(G)`.
Uses `fiedler_vector_exists` + `sweep_cut_bound` to find a cut with low expansion,
then bounds the conductance. -/
lemma cheeger_inequality
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2) :
    conductance G hV ^ 2 / (2 * ↑G.maxDegree) ≤ algebraicConnectivity G hV := by
  -- Get Fiedler vector and sweep cut bound
  obtain ⟨f, hf, hfsum, hfeig⟩ := fiedler_vector_exists G hconn hV
  obtain ⟨S, hSne, hScne, hScard, hbound⟩ :=
    sweep_cut_bound G hconn hV f hf hfsum hfeig
  -- hbound : |∂S|/|S| ≤ √(2λ₂Δ)
  -- conductance ≤ |∂S|/|S| (S is a valid cut, conductance is the infimum)
  have hcond_le : conductance G hV ≤
      Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) := by
    -- conductance = inf over valid cuts of |∂S|/|S|, and S is a valid cut
    calc conductance G hV
      _ ≤ ↑(edgeBoundary G S).card / ↑S.card := by
          unfold conductance
          exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Finset.card_pos.mpr hSne, Finset.card_pos.mpr hScne, hScard⟩)
      _ ≤ Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) := hbound
  -- h ≤ √(2λ₂Δ) → h² ≤ 2λ₂Δ → h²/(2Δ) ≤ λ₂
  have hac_nn : (0 : ℝ) ≤ algebraicConnectivity G hV :=
    le_of_lt (algebraicConnectivity_pos G hconn hV)
  have hΔ_nn : (0 : ℝ) ≤ ↑G.maxDegree := Nat.cast_nonneg _
  -- h² ≤ (√(2λ₂Δ))² = 2λ₂Δ
  have hsq : conductance G hV ^ 2 ≤
      2 * algebraicConnectivity G hV * ↑G.maxDegree := by
    calc conductance G hV ^ 2
      _ ≤ Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) ^ 2 := by
          have hcond_nn : (0 : ℝ) ≤ conductance G hV := by
            unfold conductance
            apply Finset.le_inf'; intro S hS; positivity
          exact pow_le_pow_left₀ hcond_nn hcond_le 2
      _ = 2 * algebraicConnectivity G hV * ↑G.maxDegree :=
          Real.sq_sqrt (by positivity)
  -- h²/(2Δ) ≤ λ₂
  by_cases hΔ : G.maxDegree = 0
  · simp [hΔ]; exact hac_nn
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ↑G.maxDegree)]
    linarith

/-- **Paper 12 — Theorem 1**: λ₂(L) ≥ 2(τ+1)²/(n²Δ³).

A lower bound on the algebraic connectivity (second smallest Laplacian eigenvalue)
in terms of `tauG`, the vertex count `n`, and the maximum degree `Δ`.
When `tauG G ≥ k`, the bound gives a positive spectral gap, implying robust connectivity.
See Zenodo DOI 10.5281/zenodo.18998928.

*Proof*: Chains `conductance_lower_bound → cheeger_inequality`; the final arithmetic is
`(2(k+1)/n)² / (2Δ) = 2(k+1)²/(n²Δ³)`. Fully proved (sorry-free). -/
theorem lambda2_lower_bound
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2) (k : ℕ)
    (hk : tauG G ≥ k) :
    let n := Fintype.card V
    let Δ := G.maxDegree
    (2 * (↑k + 1) ^ 2 : ℝ) / (↑n ^ 2 * ↑Δ ^ 3) ≤ algebraicConnectivity G hV := by
  -- Chain: conductance_lower_bound + cheeger_inequality
  have hcond := conductance_lower_bound G hconn hV k hk
  -- hcond : 2(k+1)/n ≤ h(G)
  have hcheeger := cheeger_inequality G hconn hV
  -- hcheeger : h²/(2Δ) ≤ λ₂
  -- λ₂ ≥ h²/(2Δ) ≥ (2(k+1)/n)²/(2Δ) ≥ 2(k+1)²/(n²Δ³)
  calc (2 * (↑k + 1) ^ 2 : ℝ) / (↑(Fintype.card V) ^ 2 * ↑G.maxDegree ^ 3)
    _ ≤ (2 * (↑k + 1) ^ 2) / (↑(Fintype.card V) ^ 2 * ↑G.maxDegree) := by
        -- 2(k+1)²/(n²Δ³) ≤ 2(k+1)²/(n²Δ) since n²Δ ≤ n²Δ³
        by_cases hΔ : G.maxDegree = 0
        · simp [hΔ]
        · have hΔ1 : (1 : ℝ) ≤ ↑G.maxDegree := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hΔ
          have hn2 : (0 : ℝ) ≤ ↑(Fintype.card V) ^ 2 := sq_nonneg _
          have key : ↑(Fintype.card V) ^ 2 * ↑G.maxDegree ≤
              ↑(Fintype.card V) ^ 2 * (↑G.maxDegree : ℝ) ^ 3 := by
            apply mul_le_mul_of_nonneg_left _ hn2
            calc (↑G.maxDegree : ℝ)
              _ = ↑G.maxDegree * 1 := by ring
              _ ≤ ↑G.maxDegree * ↑G.maxDegree ^ 2 := by
                  apply mul_le_mul_of_nonneg_left _ (by linarith)
                  nlinarith
              _ = ↑G.maxDegree ^ 3 := by ring
          exact div_le_div_of_nonneg_left (by positivity)
            (by positivity : (0 : ℝ) < ↑(Fintype.card V) ^ 2 * ↑G.maxDegree) key
    _ = ((2 * (↑k + 1)) / ↑(Fintype.card V)) ^ 2 / (2 * ↑G.maxDegree) := by ring
    _ ≤ conductance G hV ^ 2 / (2 * ↑G.maxDegree) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hcond 2
    _ ≤ algebraicConnectivity G hV := hcheeger

end Topostability
