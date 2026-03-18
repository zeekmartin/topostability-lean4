import Topostability.Defs
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Algebra.Order.Chebyshev

set_option linter.style.longFile 2000

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Laplacian matrix of a simple graph over ℝ is Hermitian (symmetric). -/
lemma isHermitian_lapMatrix : (G.lapMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact G.isSymm_lapMatrix

/-- The algebraic connectivity of `G` is the second smallest eigenvalue of the
Laplacian matrix. This requires at least 2 vertices. Since `eigenvalues₀` is
antitone, index `card V - 2` is the second smallest. -/
noncomputable def algebraicConnectivity (hV : Fintype.card V ≥ 2) : ℝ :=
  (isHermitian_lapMatrix G).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩

/-- **Conjecture 1** (Paper 11): For every connected graph `G` on at least 2 vertices,
`tauG G ≤ algebraicConnectivity G`. -/
theorem conjecture_tauG_le_algebraicConnectivity
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2) :
    (tauG G : ℝ) ≤ algebraicConnectivity G hV := by
  sorry

/-- The original statement `tauG G = 0 ↔ ∃ u v, G.Adj u v ∧ alwaysFragile G u v = true`
is false for edgeless graphs: `tauG` returns 0 by default when there are no edges, but the
RHS requires an edge to exist. We add `G.edgeFinset.Nonempty` as a hypothesis. -/
lemma tauG_eq_zero_iff (he : G.edgeFinset.Nonempty) :
    tauG G = 0 ↔ ∃ u v, G.Adj u v ∧ alwaysFragile G u v = true := by
  simp only [tauG, dif_pos he, alwaysFragile, beq_iff_eq]
  constructor
  · intro h0
    obtain ⟨e, hem, heq⟩ := Finset.exists_mem_eq_inf' he (triCountSym2 G)
    rw [h0] at heq
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hem
      refine ⟨u, v, hem, ?_⟩
      simp only [triCountSym2, Sym2.lift_mk] at heq
      exact heq.symm
  · rintro ⟨u, v, hadj, h0⟩
    have hmem : s(u, v) ∈ G.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr hadj
    have hle := Finset.inf'_le (triCountSym2 G) hmem
    have hzero : triCountSym2 G s(u, v) = 0 := by
      simp only [triCountSym2, Sym2.lift_mk]
      exact h0
    omega

/-- The converse (`tauG G = 0 → ∃ bridge`) is **false**: C4 (4-cycle) is connected with
`tauG = 0` (every edge has 0 common neighbors), yet no edge is a bridge — removing any
single edge from a cycle leaves a path, which is still connected.

This theorem states the correct direction: a bridge edge has no common neighbors
(any common neighbor `w` would give an alternative path `u–w–v` surviving deletion),
so `triCount = 0` on that edge, forcing `tauG ≤ triCount = 0`. -/
theorem bridge_implies_tauG_zero
    (hconn : G.Connected) {u v : V} (h : G.Adj u v)
    (hbridge : ¬ (G.deleteEdges {s(u, v)}).Connected)
    (hne : G.edgeFinset.Nonempty) :
    tauG G = 0 := by
  rw [tauG_eq_zero_iff G hne]
  refine ⟨u, v, h, ?_⟩
  simp only [alwaysFragile, beq_iff_eq, triCount, Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro w hw
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
  obtain ⟨huw, hvw⟩ := hw
  -- From ¬Connected after deletion + G.Connected, deduce IsBridge.
  have hb : G.IsBridge s(u, v) := by
    by_contra hnb
    exact hbridge (hconn.connected_delete_edge_of_not_isBridge hnb)
  rw [SimpleGraph.isBridge_iff] at hb
  -- IsBridge gives ¬ Reachable u v in the deleted graph.
  -- We derive a contradiction by building a path u — w — v that survives deletion.
  apply hb.2
  have adj_uw : (G.deleteEdges {s(u, v)}).Adj u w := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨huw, by
      rw [Set.mem_singleton_iff]
      intro heq
      have : w ∈ s(u, v) := heq ▸ Sym2.mem_mk_right u w
      rw [Sym2.mem_iff] at this
      rcases this with rfl | rfl
      · exact huw.ne rfl
      · exact hvw.ne rfl⟩
  have adj_wv : (G.deleteEdges {s(u, v)}).Adj w v := by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hvw.symm, by
      rw [Set.mem_singleton_iff]
      intro heq
      have : w ∈ s(u, v) := heq ▸ Sym2.mem_mk_left w v
      rw [Sym2.mem_iff] at this
      rcases this with rfl | rfl
      · exact huw.ne rfl
      · exact hvw.ne rfl⟩
  exact adj_uw.reachable.trans adj_wv.reachable

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

/-! ### Spectral bridge: quadratic form = eigenvalue sum -/

/-- **Spectral decomposition of the quadratic form**: `xᵀLx = Σᵢ λᵢ cᵢ²`
where `λᵢ` are eigenvalues and `cᵢ` are coordinates in the eigenbasis.

This bridges `Matrix.toLinearMap₂'` (operating on `V → ℝ`) with the
spectral decomposition (operating on `EuclideanSpace ℝ V`). -/
lemma rayleigh_eq_eigensum (x : V → ℝ) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x =
      ∑ i : V, (isHermitian_lapMatrix G).eigenvalues i *
        ((isHermitian_lapMatrix G).eigenvectorBasis.repr
          (WithLp.toLp 2 x) i) ^ 2 := by
  set hL := isHermitian_lapMatrix G
  set B := hL.eigenvectorBasis
  set L := G.lapMatrix ℝ
  set v : EuclideanSpace ℝ V := WithLp.toLp 2 x
  set T := L.toEuclideanLin
  set hT := Matrix.isHermitian_iff_isSymmetric.1 hL
  -- Step 1-2: toLinearMap₂' = ⟪v, T v⟫
  have h1 : Matrix.toLinearMap₂' ℝ L x x = @inner ℝ _ _ v (T v) := by
    rw [Matrix.toLinearMap₂'_apply']
    -- After unfolding, both sides are dotProduct up to commutativity
    change dotProduct x (L.mulVec x) = @inner ℝ _ _ v (T v)
    -- inner (toLp x) (toLp (L *ᵥ x)) = dotProduct (L *ᵥ x) x  [by def]
    -- so we need dotProduct x (L *ᵥ x) = dotProduct (L *ᵥ x) x
    exact dotProduct_comm x (L.mulVec x)
  rw [h1]
  -- Step 3: repr preserves inner product
  rw [← B.repr.inner_map_map v (T v)]
  -- Step 4-6: expand inner product and apply eigenvalue decomposition
  -- PiLp.inner_apply is rfl: ⟪x, y⟫_PiLp = ∑ i, ⟪x i, y i⟫_ℝ
  show (∑ i : V, @inner ℝ ℝ _ ((B.repr v) i) ((B.repr (T v)) i)) =
    ∑ i : V, hL.eigenvalues i * ((B.repr v).ofLp i) ^ 2
  refine Finset.sum_congr rfl fun i _ => ?_
  -- Step 5: B.repr (T v) i = ⟪B i, T v⟫ = ⟪T(B i), v⟫ = λᵢ * ⟪B i, v⟫ = λᵢ * B.repr v i
  have hrepr : B.repr (T v) i = hL.eigenvalues i * B.repr v i := by
    simp only [OrthonormalBasis.repr_apply_apply]
    rw [← hT (B i) v]
    have hTB : T (B i) = (hL.eigenvalues i : ℝ) • B i := by
      have h := hL.mulVec_eigenvectorBasis i
      ext j; exact (congr_fun h j).trans (Pi.smul_apply _ _ _)
    rw [hTB]; erw [inner_smul_left_eq_smul, smul_eq_mul]; rfl
  rw [hrepr, show hL.eigenvalues i * (B.repr v).ofLp i =
    hL.eigenvalues i • (B.repr v).ofLp i from (smul_eq_mul _ _).symm]
  erw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  simp [Real.norm_eq_abs, sq_abs]

/-! ### Courant–Fischer for λ₂

The key spectral lemma: `algebraicConnectivity` (= second-smallest eigenvalue
of the Laplacian) is at most the Rayleigh quotient of any test vector orthogonal
to the constant vector. This is the upper-bound direction of Courant–Fischer. -/

/-- For any nonzero vector `x` orthogonal to the all-ones vector,
`algebraicConnectivity G ≤ xᵀLx / ‖x‖²`.

This uses the spectral decomposition: in the eigenbasis `{e₀,…,eₙ₋₁}` with
eigenvalues `λ₀ ≥ … ≥ λₙ₋₁ = 0`, write `x = Σ cᵢeᵢ`. Since `x ⊥ eₙ₋₁`
(the constant eigenvector for connected G), `cₙ₋₁ = 0`. Then
`xᵀLx = Σᵢ λᵢcᵢ² ≥ λₙ₋₂ Σᵢ cᵢ² = λ₂ ‖x‖²`.

**Proof status**: The spectral decomposition exists in Mathlib
(`eigenvectorBasis_apply_self_apply`), but connecting it to
`star x ⬝ᵥ A *ᵥ x` for arbitrary `x` requires ~50 lines of
`OrthonormalBasis.repr` manipulation and `EuclideanSpace` ↔ `V → ℝ`
type conversions that are not yet bridged by existing API. -/
lemma algebraicConnectivity_le_rayleigh
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (x : V → ℝ) (hx : x ≠ 0) (horth : ∑ v : V, x v = 0) :
    algebraicConnectivity G hV ≤
      Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x / (∑ v, x v ^ 2) := by
  set hL := isHermitian_lapMatrix G
  set B := hL.eigenvectorBasis
  -- Step 1: rewrite numerator as ∑ λᵢcᵢ² using spectral bridge
  rw [rayleigh_eq_eigensum]
  -- Step 2: ∑ xᵢ² > 0
  have hxsq_pos : 0 < ∑ v : V, x v ^ 2 := by
    apply Finset.sum_pos'  (fun i _ => sq_nonneg (x i))
    obtain ⟨v, hv⟩ : ∃ v, x v ≠ 0 := by
      by_contra h; push_neg at h; exact hx (funext h)
    exact ⟨v, Finset.mem_univ _, by positivity⟩
  -- Step 3: Parseval — ∑ xᵢ² = ∑ cᵢ² (repr is linear isometry)
  set v : EuclideanSpace ℝ V := WithLp.toLp 2 x
  set c : V → ℝ := fun i => (B.repr v).ofLp i
  have hparseval : ∑ w : V, x w ^ 2 = ∑ i : V, c i ^ 2 := by
    have h1 : ∑ w : V, x w ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    have h2 : ∑ i : V, c i ^ 2 = ‖B.repr v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [h1, h2, LinearIsometryEquiv.norm_map]
  rw [hparseval]
  -- Step 4: ac ≤ (∑ λᵢcᵢ²) / (∑ cᵢ²)  ↔  ac * ∑ cᵢ² ≤ ∑ λᵢcᵢ²
  rw [le_div_iff₀ (by rwa [← hparseval])]
  -- Step 5: per-term bound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hge : algebraicConnectivity G hV ≤ hL.eigenvalues i
  · -- Case: λᵢ ≥ ac → ac·cᵢ² ≤ λᵢ·cᵢ²
    exact mul_le_mul_of_nonneg_right hge (sq_nonneg _)
  · -- Case: λᵢ < ac → eigenvalue must be 0 → eigenvector constant → cᵢ = 0
    push_neg at hge
    -- eigenvalues i = 0 (only possible value < ac for Laplacian)
    -- Proof: det L = 0 (nonempty V), all eigenvalues ≥ 0 (posSemidef),
    -- so min eigenvalue = 0. Any eigenvalue < ac (2nd smallest) must be 0.
    have hev0 : hL.eigenvalues i = 0 := by
      -- Step A: 0 ≤ eigenvalues i (positive semidefinite)
      have hnn : (0 : ℝ) ≤ hL.eigenvalues i :=
        (SimpleGraph.posSemidef_lapMatrix ℝ G).eigenvalues_nonneg i
      -- Step B: eigenvalues i ≤ 0
      -- Unfold: eigenvalues i = eigenvalues₀[equiv i]
      -- where equiv = (equivOfCardEq ...).symm
      -- Unfold eigenvalues to eigenvalues₀
      show hL.eigenvalues₀
        ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) = 0
      set e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm
        with he_def
      change hL.eigenvalues₀ (e i) = 0
      have hanti := hL.eigenvalues₀_antitone
      -- hge gives eigenvalues₀[e i] < eigenvalues₀[card-2]
      have hge' : hL.eigenvalues₀ (e i) <
          hL.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ := hge
      -- By antitone: (e i).val > card V - 2, so (e i).val = card V - 1
      have hidx : (e i).val ≥ Fintype.card V - 1 := by
        by_contra h; push_neg at h
        have : e i ≤ ⟨Fintype.card V - 2, by omega⟩ := by
          simp [Fin.le_def]; omega
        exact absurd (hanti this) (not_le.mpr hge')
      have heq : e i = ⟨Fintype.card V - 1, by omega⟩ := by
        ext; simp only [Fin.val_mk]; omega
      rw [heq]
      -- eigenvalues₀[last] = 0: minimum of nonneg sequence with zero det
      apply le_antisymm _ (heq ▸ hnn)
      -- Need: eigenvalues₀[last] ≤ 0
      -- det L = 0 → ∃ j with eigenvalues j = 0 → eigenvalues₀[last] ≤ 0
      haveI : Nonempty V := hconn.nonempty
      have hdet : (G.lapMatrix ℝ).det = 0 := SimpleGraph.det_lapMatrix_eq_zero G
      rw [hL.det_eq_prod_eigenvalues] at hdet
      -- ∏ (eigenvalues j : ℝ) = 0 → ∃ j, eigenvalues j = 0
      -- ∏ (eigenvalues j : ℝ) = 0 → ∃ j, eigenvalues j = 0
      obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp (show ∏ j : V,
        hL.eigenvalues j = 0 from by exact_mod_cast hdet)
      -- eigenvalues₀[last] ≤ eigenvalues₀[j] = 0 (antitone + last is max index)
      have : hL.eigenvalues₀ ⟨Fintype.card V - 1, by omega⟩ ≤
          hL.eigenvalues₀ (e j) :=
        hanti (Fin.le_def.mpr (by simp [Fin.val_mk]; omega))
      linarith [show hL.eigenvalues₀ (e j) = 0 from by
        simp [Matrix.IsHermitian.eigenvalues] at hj; exact hj]
    -- L *ᵥ (B i) = 0 → B i is constant (connected G)
    have hBker : (G.lapMatrix ℝ).mulVec ((B i).ofLp) = 0 := by
      have := hL.mulVec_eigenvectorBasis i
      simp [hev0] at this; exact this
    have hBconst : ∀ j : V, (B i).ofLp j =
        (B i).ofLp hconn.nonempty.some := by
      intro j
      exact (SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable G).mp
        hBker j _ (hconn.preconnected j _)
    -- B i constant + ∑ x = 0 → c i = ⟪B i, x⟫ = const · ∑ x = 0
    have hci : c i = 0 := by
      -- c i = B.repr v i = ⟪B i, v⟫ = ∑ w, (B i) w * x w
      simp only [c, WithLp.ofLp, OrthonormalBasis.repr_apply_apply, v]
      show (∑ w : V, @inner ℝ ℝ _ ((B i) w) ((WithLp.toLp 2 x) w)) = 0
      -- Factor out constant (B i) value
      have : ∀ w, @inner ℝ ℝ _ ((B i) w) ((WithLp.toLp 2 x) w) =
          (B i).ofLp hconn.nonempty.some * x w := fun w => by
        simp only [inner, one_mul, WithLp.ofLp, RCLike.re_to_real,
          starRingEnd_apply, star_trivial, mul_comm (x w)]
        rw [hBconst w]
      simp_rw [this, ← Finset.mul_sum, horth, mul_zero]
    show algebraicConnectivity G hV * c i ^ 2 ≤
      hL.eigenvalues i * c i ^ 2
    rw [hci]; simp

/-- The algebraic connectivity is strictly positive for connected graphs with ≥ 2 vertices.
Proof: connected → 1 component → dim ker L = 1 → exactly 1 zero eigenvalue → λ₂ > 0. -/
lemma algebraicConnectivity_pos
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2) :
    0 < algebraicConnectivity G hV := by
  set hL := isHermitian_lapMatrix G
  set L := G.lapMatrix ℝ
  -- Step 1: finrank ker L = 1 (connected G has 1 component)
  have hker : Module.finrank ℝ (LinearMap.ker L.toLin') = 1 := by
    rw [← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
    letI := hconn.preconnected.subsingleton_connectedComponent
    haveI : Unique G.ConnectedComponent :=
      uniqueOfSubsingleton (G.connectedComponentMk hconn.nonempty.some)
    exact Fintype.card_unique
  -- Step 2: #{zero eigenvalues} = 1
  -- Bridge toLin' ↔ mulVecLin for rank-nullity
  have hone_zero : Fintype.card {i : V // hL.eigenvalues i = 0} = 1 := by
    have hrank := hL.rank_eq_card_non_zero_eigs
    -- rank L = #{nonzero eigenvalues}
    -- rank L = card V - finrank ker L = card V - 1 (rank-nullity)
    have hrn : L.rank + Module.finrank ℝ (LinearMap.ker L.mulVecLin) = Fintype.card V := by
      rw [Matrix.rank]
      have := L.mulVecLin.finrank_range_add_finrank_ker
      simp only [Module.finrank_pi_fintype, Module.finrank_self,
        Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at this
      exact this
    -- Connect toLin' ker to mulVecLin ker
    have hker2 : Module.finrank ℝ (LinearMap.ker L.mulVecLin) = 1 := by
      rwa [show L.toLin' = L.mulVecLin from by ext v; rfl] at hker
    -- #{nonzero} = card V - 1, #{zero} = 1
    have := Fintype.card_subtype_compl (p := fun i : V => hL.eigenvalues i ≠ 0)
    simp only [not_not] at this; omega
  -- Step 3: eigenvalues₀[card-2] > 0 by contradiction
  unfold algebraicConnectivity
  by_contra h; push_neg at h
  -- eigenvalues₀[card-2] = 0 (from ≤ 0 and ≥ 0)
  -- eigenvalues₀ nonneg from PosSemidef + eigenvalues connection
  have hnn₀ : ∀ j, (0 : ℝ) ≤ hL.eigenvalues₀ j := by
    intro j
    -- eigenvalues₀ j = eigenvalues (equiv j) ≥ 0 by PosSemidef
    have h := (SimpleGraph.posSemidef_lapMatrix ℝ G).eigenvalues_nonneg
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
    convert h using 1; simp [Matrix.IsHermitian.eigenvalues]
  have h0 : hL.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ = 0 := le_antisymm h (hnn₀ _)
  -- eigenvalues₀[card-1] = 0 (antitone + nonneg)
  have h1 : hL.eigenvalues₀ ⟨Fintype.card V - 1, by omega⟩ = 0 :=
    le_antisymm (h0 ▸ hL.eigenvalues₀_antitone (Fin.mk_le_mk.mpr (by omega))) (hnn₀ _)
  -- Two distinct V-indices with eigenvalue 0
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))
  have hz1 : hL.eigenvalues (e ⟨Fintype.card V - 2, by omega⟩) = 0 := by
    show hL.eigenvalues₀ _ = 0
    convert h0 using 2; simp [e, Equiv.symm_apply_apply]
  have hz2 : hL.eigenvalues (e ⟨Fintype.card V - 1, by omega⟩) = 0 := by
    show hL.eigenvalues₀ _ = 0
    convert h1 using 2; simp [e, Equiv.symm_apply_apply]
  -- These are distinct (e is injective)
  have hne : e ⟨Fintype.card V - 2, by omega⟩ ≠ e ⟨Fintype.card V - 1, by omega⟩ :=
    e.injective.ne (by intro h; simp [Fin.ext_iff] at h; omega)
  -- Contradicts hone_zero = 1
  linarith [show 2 ≤ Fintype.card {i : V // hL.eigenvalues i = 0} from by
    rw [show Fintype.card {i : V // hL.eigenvalues i = 0} =
      Finset.card (Finset.univ.filter (fun i => hL.eigenvalues i = 0)) from by
        simp [Fintype.card_subtype]]
    apply Finset.one_lt_card.mpr
    exact ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz1⟩,
      _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz2⟩, hne⟩]

/-- The Fiedler vector: eigenvector for λ₂ with zero sum.
Exists from `eigenvectorBasis` at the second-to-last index. -/
lemma fiedler_vector_exists
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2) :
    ∃ f : V → ℝ, f ≠ 0 ∧ (∑ v : V, f v = 0) ∧
      (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f := by
  set hL := isHermitian_lapMatrix G
  set B := hL.eigenvectorBasis
  set idx : V := (Fintype.equivOfCardEq (Fintype.card_fin _))
    ⟨Fintype.card V - 2, by omega⟩
  refine ⟨(B idx).ofLp, ?_, ?_, ?_⟩
  · -- (a) f ≠ 0: orthonormal basis vectors are nonzero
    intro h
    exact B.orthonormal.ne_zero idx (show (B idx : EuclideanSpace ℝ V) = 0 from by
      ext j; exact congr_fun h j)
  · -- (b) ∑ f = 0: sum the eigenvalue equation, use column-sum = 0
    have heig := hL.mulVec_eigenvectorBasis idx
    -- heig: L *ᵥ ⇑(B idx) = eigenvalues idx • ⇑(B idx)
    -- Sum both sides: ∑ (L *ᵥ f) = ∑ (λ • f) = λ * ∑ f
    -- ∑ (L *ᵥ f) = 0 (column sums of symmetric L are 0)
    -- So λ * ∑ f = 0. Since λ = ac ≠ 0, ∑ f = 0.
    -- Sum the eigenvalue equation: λ * ∑ f = ∑ (L *ᵥ f) = 0
    suffices h : hL.eigenvalues idx * ∑ v : V, (B idx).ofLp v = 0 by
      exact (mul_eq_zero.mp h).resolve_left (by
        exact ne_of_gt (show (0 : ℝ) < hL.eigenvalues idx from by
          convert algebraicConnectivity_pos G hconn hV using 2
          simp [idx, algebraicConnectivity, Matrix.IsHermitian.eigenvalues]))
    -- Sum heig: ∑ (L *ᵥ f) v = ∑ (λ • f) v = λ * ∑ f v
    have hsum := congr_arg (fun g => ∑ w : V, g w) heig
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hsum
    -- ∑ (L *ᵥ f) = 0: use symmetry of L and L *ᵥ 1 = 0
    linarith [show ∑ w : V, (G.lapMatrix ℝ).mulVec ((B idx).ofLp) w = 0 from by
      have h1 := SimpleGraph.lapMatrix_mulVec_const_eq_zero (R := ℝ) G
      -- ∑ w, (L *ᵥ f) w = 1 ⬝ᵥ (L *ᵥ f) = (Lᵀ *ᵥ 1) ⬝ᵥ f = (L *ᵥ 1) ⬝ᵥ f = 0
      simp only [show ∑ w : V, (G.lapMatrix ℝ).mulVec ((B idx).ofLp) w =
        dotProduct (fun _ => (1 : ℝ)) ((G.lapMatrix ℝ).mulVec ((B idx).ofLp)) from by
          simp [dotProduct]]
      rw [Matrix.dotProduct_mulVec]
      -- vecMul 1 L = 0 (column sums = row sums = 0 for symmetric L)
      rw [show Matrix.vecMul (fun _ => (1 : ℝ)) (G.lapMatrix ℝ) = 0 from by
        ext j; simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
        rw [show ∑ i, (1 : ℝ) * (G.lapMatrix ℝ) i j =
          ∑ i, (G.lapMatrix ℝ) j i from by
            simp_rw [one_mul]
            exact Finset.sum_congr rfl fun i _ =>
              G.isSymm_lapMatrix.apply j i]
        simpa [Matrix.mulVec, dotProduct] using congr_fun h1 j]
      simp [dotProduct]]
  · -- (c) L *ᵥ f = ac • f: from mulVec_eigenvectorBasis
    have := hL.mulVec_eigenvectorBasis idx
    -- eigenvalues idx = ac by definition; ⇑(B idx) = (B idx).ofLp
    convert this using 2
    simp [idx, algebraicConnectivity, Matrix.IsHermitian.eigenvalues]

/-- **TASK 2**: Sweep cut — the level set `{v : f(v) ≥ t}`. -/
noncomputable def sweepCut (f : V → ℝ) (t : ℝ) : Finset V :=
  Finset.univ.filter (fun v => t ≤ f v)

/-! ### Sweep cut sub-lemmas (architecture for Cheeger hard direction)

The proof of `sweep_cut_bound` decomposes into the following chain:
1. Quadratic form = sum over edges (already proved as `cutTestVec_laplacian`)
2. Discrete coarea: ∑ |f(u)-f(v)| over edges = ∑ over thresholds of |∂S_t|
3. Cauchy–Schwarz on each boundary
4. Pigeonhole to find optimal threshold -/

/-- **Sub-lemma 1**: Quadratic form = sum over edges of (f(u)-f(v))². -/
lemma quadratic_form_eq_edge_sum (f : V → ℝ) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f =
      ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2,
          fun u v => by ring⟩ e := by
  rw [SimpleGraph.lapMatrix_toLinearMap₂']
  -- Goal: (∑ i j, [Adj i j](f i - f j)²) / 2 = ∑ e ∈ edgeFinset, Sym2.lift(...)e
  -- Strategy: double sum / 2 = (∑ darts g) / 2 = (2 * ∑ edges g) / 2 = ∑ edges g
  classical
  -- Suffices: double sum = 2 * edge sum, then (2S)/2 = S
  suffices h : ∑ i : V, ∑ j : V,
      (if G.Adj i j then (f i - f j) ^ 2 else (0 : ℝ)) =
      2 * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e by
    linarith
  -- Use hsplit from cutTestVec_laplacian: split (i∈S)≠(j∈S) into two disjoint sums.
  -- Here: split the double sum by swapping i↔j in one copy.
  classical
  -- Step 1: ∑∑ [Adj] g = ∑_darts g (convert indicator sum to dart sum)
  have h1 : ∑ i : V, ∑ j : V,
      (if G.Adj i j then (f i - f j) ^ 2 else (0 : ℝ)) =
      ∑ d : G.Dart, (f d.fst - f d.snd) ^ 2 := by
    -- Dart sum = fiberwise sum by d.fst = vertex sum
    symm; simp_rw [← Finset.sum_filter]
    -- RHS: ∑ v, ∑ a ∈ filter(Adj v), (f v - f a)²
    -- LHS (after fiberwise): ∑ v, ∑ d ∈ {d | d.fst = v}, (f d.fst - f d.snd)²
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun (d : G.Dart) => d.fst)
        (f := fun d => (f d.fst - f d.snd) ^ 2)
        (fun _ _ => Finset.mem_univ _)]
    -- Per vertex: ∑_{d | d.fst = v} g d = ∑_{w | Adj v w} g(v,w)
    congr 1 with v
    -- Use dart_fst_fiber: {d | d.fst = v} = image(dartOfNeighborSet v)
    rw [G.dart_fst_fiber v, Finset.sum_image (fun _ _ _ _ h =>
      G.dartOfNeighborSet_injective v h)]
    -- ∑ w : neighborSet v, g(dartOfNeighborSet v w) = ∑ w ∈ filter(Adj v), g(v,w)
    -- dartOfNeighborSet v w = ⟨(v, ↑w), w.prop⟩
    simp only [SimpleGraph.dartOfNeighborSet]
    -- neighborSet v ↔ neighborFinset v: convert sum over Set subtype to Finset
    simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter,
      SimpleGraph.mem_neighborSet]
    -- ∑ x : neighborSet v, g ↑x = ∑ a : V, if Adj v a then g a else 0
    -- ∑ x : {w | P w}, g ↑x = ∑ a, if P a then g a else 0
    -- ∑ x : {w | Adj v w}, g ↑x = ∑ a : V, if Adj v a then g a else 0
    -- This is Finset.sum over subtype = Finset.sum with ite indicator
    -- ∑ x : neighborSet v, g ↑x = ∑ a, if Adj v a then g a else 0
    -- Proved by: both sides sum the same function over {w | Adj v w}
    -- LHS: ∑ x : neighborSet v, g ↑x
    -- RHS: ∑ a : V, if Adj v a then g a else 0 = ∑ a ∈ filter(Adj v), g a
    -- Convert RHS from ite to filter form, then use sum_subtype
    conv_rhs => rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (G.Adj v))
      (fun w => by simp [SimpleGraph.mem_neighborSet])
      (fun w => (f v - f w) ^ 2)).symm
  -- Step 2: ∑_darts g = 2 * ∑_edges g (each edge has 2 darts)
  have h2 : ∑ d : G.Dart, (f d.fst - f d.snd) ^ 2 =
      2 * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e := by
    rw [Finset.mul_sum, ← Finset.sum_fiberwise_of_maps_to
      (g := fun (d : G.Dart) => d.edge) (s := Finset.univ)
      (t := G.edgeFinset) (fun d _ => SimpleGraph.mem_edgeFinset.mpr d.edge_mem)]
    apply Finset.sum_congr rfl; intro e he
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
      simp only [Sym2.lift_mk, d₀, SimpleGraph.Dart.symm, Prod.swap]; ring
  linarith [h1, h2]

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

/-- **Sub-lemma 5**: Pigeonhole — ∃ good threshold. -/
lemma sweep_pigeonhole
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (f : V → ℝ) (hf : f ≠ 0) (hfsum : ∑ v : V, f v = 0)
    (hfeig : (G.lapMatrix ℝ).mulVec f = algebraicConnectivity G hV • f) :
    ∃ (S : Finset V), S.Nonempty ∧ Sᶜ.Nonempty ∧
      S.card ≤ Fintype.card V / 2 ∧
      ((edgeBoundary G S).card : ℝ) / ↑S.card ≤
        Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) := by
  -- Step 1: Sorting permutation σ ordering vertices by f-values
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (Fintype.card V) ≃ V,
      ∀ i j : Fin (Fintype.card V), i ≤ j → f (σ i) ≤ f (σ j) := by
    sorry -- Standard: sort V by f-values
  -- Step 2: Assemble proved bounds
  -- Discrete coarea: ∑_e |f u - f v| = ∑_k gap_k * |∂S_k|
  have hcoarea := discrete_coarea G f σ hσ hV
  -- Edge-degree bound: ∑_e (f u - f v)² ≤ 2Δ ‖f‖²
  have hΔ := edge_degree_bound G f
  -- Quadratic form = edge sum (proved)
  have hquad := quadratic_form_eq_edge_sum G f
  -- Eigenvalue equation gives: ∑_e (fu-fv)² = λ₂ ‖f‖²
  have heig_eq : algebraicConnectivity G hV * ∑ v : V, f v ^ 2 =
      ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e := by
    rw [← hquad]
    -- toLinearMap₂' L f f = f ⬝ (L *ᵥ f) = f ⬝ (λ₂ • f) = λ₂ * (f ⬝ f)
    sorry -- bilinear form with eigenvector equation Lf = λ₂f
  -- Step 3: Each sweep cut S_k = {v | f v ≥ f(σ(k+1))} is nonempty
  have hSne : ∀ k : Fin (Fintype.card V - 1),
      (Finset.univ.filter fun w => f w ≥ f (σ ⟨k.val + 1, by omega⟩)).Nonempty :=
    fun k => ⟨σ ⟨k.val + 1, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _⟩⟩
  -- Step 4: Pigeonhole — ∃ k with complement nonempty, |S_k| ≤ n/2,
  -- and |∂S_k|/|S_k| ≤ √(2λ₂Δ)
  -- Uses hcoarea, heig_eq, hΔ, hfsum, and Cauchy–Schwarz (boundary_cauchy_schwarz)
  obtain ⟨k, hcne, hcard, hbound⟩ :
      ∃ k : Fin (Fintype.card V - 1),
        (Finset.univ.filter fun w => f w ≥ f (σ ⟨k.val + 1, by omega⟩))ᶜ.Nonempty ∧
        (Finset.univ.filter fun w =>
          f w ≥ f (σ ⟨k.val + 1, by omega⟩)).card ≤ Fintype.card V / 2 ∧
        ((edgeBoundary G (Finset.univ.filter fun w =>
          f w ≥ f (σ ⟨k.val + 1, by omega⟩))).card : ℝ) /
          ↑(Finset.univ.filter fun w =>
            f w ≥ f (σ ⟨k.val + 1, by omega⟩)).card ≤
          Real.sqrt (2 * algebraicConnectivity G hV * ↑G.maxDegree) := by
    sorry -- Pigeonhole on sweep cuts using hcoarea, heig_eq, hΔ, hfsum
  -- Step 5: Provide the sweep cut witness
  exact ⟨Finset.univ.filter fun w => f w ≥ f (σ ⟨k.val + 1, by omega⟩),
    hSne k, hcne, hcard, hbound⟩

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

*Proof*: Chains `cut_multiplication → conductance_lower_bound → cheeger_inequality`.
Each step is stated above; the final arithmetic is `(2(k+1)/n)² / (2Δ) = 2(k+1)²/(n²Δ³)`.
All three steps currently use `sorry` (see individual docstrings for blockage details). -/
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

/-- Corollary of `bridge_implies_tauG_zero`: if `tauG G ≥ 1`, then no edge is a bridge.

Proof: if removing edge `{u,v}` disconnected `G`, then `bridge_implies_tauG_zero` would
give `tauG G = 0`, contradicting `tauG G ≥ 1`. -/
theorem no_bridge_of_tauG_pos
    (hconn : G.Connected) (htau : tauG G ≥ 1) (hne : G.edgeFinset.Nonempty) :
    ∀ u v, G.Adj u v → (G.deleteEdges {s(u, v)}).Connected := by
  intro u v hadj
  by_contra hbridge
  have := bridge_implies_tauG_zero G hconn hadj hbridge hne
  omega

set_option maxHeartbeats 1600000 in
private lemma directed_triangle_fiber_card (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ((Finset.univ.filter (fun t : V × V × V =>
      G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1)).filter
      (fun t => ({t.1, t.2.1, t.2.2} : Finset V) = {a, b, c})).card = 6 := by
  rw [Finset.filter_filter]
  have hba := hab.symm; have hca := hac.symm; have hcb := hbc.symm
  have h1 := G.ne_of_adj hab; have h2 := G.ne_of_adj hac; have h3 := G.ne_of_adj hbc
  -- Normalize conjunction: (A ∧ B ∧ C) ∧ D → A ∧ B ∧ C ∧ D
  simp_rw [← and_assoc]
  simp_rw [and_assoc]
  -- Show filter = explicit 6-element set, then compute card
  suffices heq : Finset.univ.filter (fun t : V × V × V =>
      G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1 ∧
      ({t.1, t.2.1, t.2.2} : Finset V) = {a, b, c}) =
    {(a,b,c),(a,c,b),(b,a,c),(b,c,a),(c,a,b),(c,b,a)} by
    rw [heq]
    simp only [Finset.card_insert_eq_ite, Finset.mem_insert, Finset.mem_singleton,
               Prod.mk.injEq, Finset.card_singleton, Finset.card_empty]
    simp [h1, h2, h3, h1.symm, h2.symm, h3.symm]
  -- Prove the filter equals the explicit set
  ext ⟨x, y, z⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
             Finset.mem_insert, Finset.mem_singleton]
  constructor
  · -- Forward: adjacency + set eq → one of 6 permutations
    rintro ⟨hxy, hyz, hzx, hset⟩
    have hx := hset ▸ show x ∈ ({x, y, z} : Finset V) by simp
    have hy := hset ▸ show y ∈ ({x, y, z} : Finset V) by simp
    have hz := hset ▸ show z ∈ ({x, y, z} : Finset V) by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
    have := G.ne_of_adj hxy; have := G.ne_of_adj hyz; have := G.ne_of_adj hzx
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl <;> tauto
  · -- Backward: one of 6 permutations → adjacency + set eq
    intro h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
                  ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      (refine ⟨?_, ?_, ?_, ?_⟩ <;>
       first | assumption
             | (ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto))

/-- **Paper 11, Theorem 1**: Spectral identity.
For any simple connected graph G with Laplacian L and adjacency matrix A:
  trace(L · A²) = Σᵢ degᵢ² - 6 * totalTriangles G -/
lemma spectral_identity :
    Matrix.trace ((G.lapMatrix ℝ) * (G.adjMatrix ℝ) ^ 2) =
    (∑ i : V, (G.degree i : ℝ) ^ 2) - 6 * (totalTriangles G : ℝ) := by
  -- Step 1: L = D - A, so trace(L·A²) = trace(D·A²) - trace(A·A²)
  have hL : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
  rw [hL, Matrix.sub_mul, Matrix.trace_sub]
  -- Step 2: trace(D · A²) = ∑ᵢ dᵢ²
  -- (D·A²)ᵢᵢ = dᵢ · (A²)ᵢᵢ = dᵢ · dᵢ (since (A²)ᵢᵢ = degᵢ for 0-1 adjacency)
  have h_deg_trace : Matrix.trace (G.degMatrix ℝ * (G.adjMatrix ℝ) ^ 2) =
      ∑ i : V, (G.degree i : ℝ) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag]
    congr 1; ext i
    simp only [sq, SimpleGraph.degMatrix, Matrix.diagonal_mul,
               SimpleGraph.adjMatrix_mul_self_apply_self]
  -- Step 3: trace(A³) = 6 · totalTriangles G
  -- (A³)ᵢᵢ counts closed walks i→j→k→i, each triangle counted 6× (3 vertices × 2 orientations)
  have h_cube_trace : Matrix.trace (G.adjMatrix ℝ * (G.adjMatrix ℝ) ^ 2) =
      6 * (totalTriangles G : ℝ) := by
    -- trace(A · A²) = ∑ᵢ ∑ⱼ ∑ₖ Aᵢⱼ · Aⱼₖ · Aₖᵢ
    --              = |{(i,j,k) : V³ | Adj i j ∧ Adj j k ∧ Adj k i}|
    --              = 6 · |cliqueFinset 3|
    -- Each undirected triangle {a,b,c} yields 6 directed triples (3 starts × 2 orientations).
    simp only [Matrix.trace, Matrix.diag, sq, Matrix.mul_apply,
               SimpleGraph.adjMatrix_apply]
    -- Goal: ∑ i, ∑ j, [Adj i j] * ∑ k, [Adj j k] * [Adj k i] = 6 * ↑(cliqueFinset 3).card
    -- Pull multiplication inside inner sum and combine indicators
    simp_rw [Finset.mul_sum]
    -- Each summand is a product of three 0-1 indicators
    -- Convert products of if-then-else to conjunction
    have h01 : ∀ (p q r : Prop) [Decidable p] [Decidable q] [Decidable r],
        (if p then (1 : ℝ) else 0) * ((if q then (1 : ℝ) else 0) *
        (if r then (1 : ℝ) else 0)) =
        if (p ∧ q ∧ r) then 1 else 0 := by
      intros; split_ifs <;> simp_all
    simp_rw [h01]
    -- Now: ∑ i j k, if (Adj i j ∧ Adj j k ∧ Adj k i) then 1 else 0 = 6 * ↑(...)
    push_cast [totalTriangles]
    -- Convert triple sum of indicators to card of filtered finset
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    rw [Finset.sum_boole]
    -- Goal: ↑#{t ∈ univ | Adj t.1 t.2.1 ∧ Adj t.2.1 t.2.2 ∧ Adj t.2.2 t.1} = 6 * ↑(cliqueFinset 3).card
    norm_cast
    -- ℕ goal: #{(i,j,k) | Adj i j ∧ Adj j k ∧ Adj k i} = 6 * |cliqueFinset 3|
    -- Map each directed triple (i,j,k) to its unordered triangle {i,j,k}
    set dirTri := Finset.univ.filter (fun t : V × V × V =>
      G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1) with hdirTri_def
    have hmap : ∀ t ∈ dirTri, ({t.1, t.2.1, t.2.2} : Finset V) ∈ G.cliqueFinset 3 := by
      intro ⟨i, j, k⟩ ht
      simp only [hdirTri_def, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
      exact ⟨ht.1, ht.2.2.symm, ht.2.1⟩
    -- Decompose by fiber: total = Σ_{s ∈ cliqueFinset 3} |fiber(s)|
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    -- Each fiber has exactly 6 elements (3! directed orderings per triangle)
    rw [Finset.sum_const_nat (m := 6) (fun s hs => ?_), mul_comm]
    -- Each fiber has card 6: use helper lemma
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hs
    rw [hdirTri_def]
    exact directed_triangle_fiber_card G a b c hab hac hbc
  rw [h_deg_trace, h_cube_trace]

/-- **Paper 11, Theorem 2**: Upper bound on λ₂ for d-regular graphs.
  λ₂(G) ≤ (n·d² - 6T) / (d·(n-d)) -/
lemma lambda2_upper_bound_regular
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (d : ℕ) (hreg : G.IsRegularOfDegree d)
    (hd : 0 < d) (hnd : d < Fintype.card V) :
    algebraicConnectivity G hV ≤
    ((Fintype.card V : ℝ) * (d : ℝ) ^ 2 - 6 * (totalTriangles G : ℝ)) /
    ((d : ℝ) * ((Fintype.card V : ℝ) - (d : ℝ))) := by
  -- Step 1: spectral_identity gives trace(L·A²) = Σdᵢ² - 6T
  have hid := spectral_identity G
  -- Step 2: For d-regular graphs, Σdᵢ² = n·d²
  have hreg_sum : ∑ i : V, (G.degree i : ℝ) ^ 2 =
      (Fintype.card V : ℝ) * (d : ℝ) ^ 2 := by
    simp_rw [hreg.degree_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Step 3: So trace(L·A²) = n·d² - 6T
  rw [hreg_sum] at hid
  -- Step 4: The denominator d·(n-d) > 0
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hnd_pos : (0 : ℝ) < (Fintype.card V : ℝ) - (d : ℝ) := by
    rw [sub_pos]; exact_mod_cast hnd
  have hdenom_pos : (0 : ℝ) < (d : ℝ) * ((Fintype.card V : ℝ) - (d : ℝ)) :=
    mul_pos hd_pos hnd_pos
  -- Step 5: Convert to multiplication form: λ₂ · d(n-d) ≤ n·d² - 6T
  rw [le_div_iff₀ hdenom_pos]
  -- Step 6: Spectral bound λ₂ · d(n-d) ≤ trace(L·A²) = n·d² - 6T
  rw [← hid]
  -- Spectral setup
  set hLH := isHermitian_lapMatrix G with hLH_def
  set ev := hLH.eigenvalues with hev_def
  -- For d-regular: degMatrix = d • 1
  have hdeg : G.degMatrix ℝ = (d : ℝ) • (1 : Matrix V V ℝ) := by
    ext i j
    simp only [SimpleGraph.degMatrix, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs with h
    · subst h; simp [hreg.degree_eq]
    · simp
  -- A = d•1 - L (for d-regular)
  have hAdL : G.adjMatrix ℝ = (d : ℝ) • (1 : Matrix V V ℝ) - G.lapMatrix ℝ := by
    have hL_eq : G.lapMatrix ℝ = (d : ℝ) • 1 - G.adjMatrix ℝ := by
      show G.degMatrix ℝ - G.adjMatrix ℝ = _; rw [hdeg]
    rw [hL_eq, sub_sub_cancel]
  -- trace(L * A²) = ∑ ev i * (d - ev i)² (spectral decomposition)
  have htrace_eq : Matrix.trace (G.lapMatrix ℝ * (G.adjMatrix ℝ) ^ 2) =
      ∑ i : V, ev i * ((d : ℝ) - ev i) ^ 2 := by
    -- Spectral setup (scoped to this proof)
    set P : Matrix V V ℝ := ↑hLH.eigenvectorUnitary with hP_def
    set Ps : Matrix V V ℝ := (star hLH.eigenvectorUnitary : Matrix V V ℝ) with hPs_def
    set Λ := Matrix.diagonal ev with hΛ_def
    have hPsP : Ps * P = 1 := Unitary.coe_star_mul_self hLH.eigenvectorUnitary
    have hPPs : P * Ps = 1 := Unitary.coe_mul_star_self hLH.eigenvectorUnitary
    -- L = P * Λ * Ps (spectral theorem)
    have hL_spec : G.lapMatrix ℝ = P * Λ * Ps := by
      have h := hLH.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at h
      have : Matrix.diagonal (RCLike.ofReal ∘ ev : V → ℝ) = Λ := by congr 1
      rw [this] at h; exact h
    -- trace(P * M * Ps) = trace M
    have htrace_inv : ∀ M : Matrix V V ℝ, Matrix.trace (P * M * Ps) = Matrix.trace M := by
      intro M; rw [Matrix.trace_mul_cycle, hPsP, Matrix.one_mul]
    -- Key product lemma: P*Y*Ps * P*Z*Ps = P*(Y*Z)*Ps
    have hProd : ∀ Y Z : Matrix V V ℝ,
        P * Y * Ps * (P * Z * Ps) = P * (Y * Z) * Ps := by
      intro Y Z
      have h : Ps * (P * (Z * Ps)) = Z * Ps := by
        rw [← Matrix.mul_assoc Ps P, hPsP, Matrix.one_mul]
      simp only [Matrix.mul_assoc, h]
    -- d•1 - Λ = diagonal(d - ev i)
    have hdiag_sub : (d : ℝ) • (1 : Matrix V V ℝ) - Λ =
        Matrix.diagonal (fun i => (d : ℝ) - ev i) := by
      ext i j
      simp only [Λ, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.diagonal_apply, smul_eq_mul]
      split_ifs with h <;> simp [h]
    -- A = P * (d•1 - Λ) * Ps
    have hA_spec : G.adjMatrix ℝ = P * ((d : ℝ) • 1 - Λ) * Ps := by
      rw [hAdL, hL_spec, Matrix.mul_sub, Matrix.sub_mul]
      congr 1
      rw [mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hPPs]
    -- L * A² = P * (Λ * (d•1 - Λ)²) * Ps
    have hLA2 : G.lapMatrix ℝ * (G.adjMatrix ℝ) ^ 2 =
        P * (Λ * ((d : ℝ) • 1 - Λ) ^ 2) * Ps := by
      rw [hL_spec, hA_spec, sq, hProd, hProd, sq]
    -- Λ * (d•1 - Λ)² = diagonal(ev i * (d - ev i)²)
    rw [hLA2, htrace_inv, hdiag_sub, sq, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    congr 1; ext i; ring
  rw [htrace_eq]
  -- ∑ (d - ev i)² = n * d (trace of A² via matrix entries + spectral)
  have hA2_trace : ∑ i : V, ((d : ℝ) - ev i) ^ 2 = (Fintype.card V : ℝ) * (d : ℝ) := by
    -- Matrix entry calculation: trace(A²) = n * d
    have h1 : Matrix.trace ((G.adjMatrix ℝ) ^ 2) = (Fintype.card V : ℝ) * (d : ℝ) := by
      simp only [Matrix.trace, Matrix.diag, sq, SimpleGraph.adjMatrix_mul_self_apply_self]
      simp [hreg.degree_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    -- Spectral calculation: trace(A²) = ∑ (d - ev i)²
    have h2 : Matrix.trace ((G.adjMatrix ℝ) ^ 2) = ∑ i : V, ((d : ℝ) - ev i) ^ 2 := by
      set P : Matrix V V ℝ := ↑hLH.eigenvectorUnitary
      set Ps : Matrix V V ℝ := (star hLH.eigenvectorUnitary : Matrix V V ℝ)
      set Λ := Matrix.diagonal ev
      have hPsP : Ps * P = 1 := Unitary.coe_star_mul_self hLH.eigenvectorUnitary
      have hPPs : P * Ps = 1 := Unitary.coe_mul_star_self hLH.eigenvectorUnitary
      have hA_spec : G.adjMatrix ℝ = P * ((d : ℝ) • 1 - Λ) * Ps := by
        rw [hAdL]
        have hL_spec : G.lapMatrix ℝ = P * Λ * Ps := by
          have h := hLH.spectral_theorem
          rw [Unitary.conjStarAlgAut_apply] at h
          have : Matrix.diagonal (RCLike.ofReal ∘ ev : V → ℝ) = Λ := by congr 1
          rw [this] at h; exact h
        rw [hL_spec, Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        rw [mul_smul_comm, Matrix.mul_one, smul_mul_assoc, hPPs]
      have hProd : ∀ Y Z : Matrix V V ℝ,
          P * Y * Ps * (P * Z * Ps) = P * (Y * Z) * Ps := by
        intro Y Z
        have h : Ps * (P * (Z * Ps)) = Z * Ps := by
          rw [← Matrix.mul_assoc Ps P, hPsP, Matrix.one_mul]
        simp only [Matrix.mul_assoc, h]
      have htrace_inv : ∀ M : Matrix V V ℝ, Matrix.trace (P * M * Ps) = Matrix.trace M := by
        intro M; rw [Matrix.trace_mul_cycle, hPsP, Matrix.one_mul]
      have hdiag_sub : (d : ℝ) • (1 : Matrix V V ℝ) - Λ =
          Matrix.diagonal (fun i => (d : ℝ) - ev i) := by
        ext i j
        simp only [Λ, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.diagonal_apply, smul_eq_mul]
        split_ifs with h <;> simp [h]
      rw [show (G.adjMatrix ℝ) ^ 2 = P * ((d : ℝ) • 1 - Λ) ^ 2 * Ps from by
        rw [hA_spec, sq, hProd, sq]]
      rw [htrace_inv, hdiag_sub, sq, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      congr 1; ext i; ring
    linarith
  -- Existence of zero eigenvalue (from det L = 0)
  haveI : Nonempty V := hconn.nonempty
  have ⟨j₀, hj₀⟩ : ∃ j₀ : V, ev j₀ = 0 := by
    have hdet : (G.lapMatrix ℝ).det = 0 := SimpleGraph.det_lapMatrix_eq_zero G
    rw [hLH.det_eq_prod_eigenvalues] at hdet
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp
      (show ∏ j : V, hLH.eigenvalues j = 0 from by exact_mod_cast hdet)
    exact ⟨j, by simp [Matrix.IsHermitian.eigenvalues] at hj; exact hj⟩
  -- Uniqueness: if ev i = 0, then i = j₀
  have huniq : ∀ i : V, ev i = 0 → i = j₀ := by
    intro i hi
    set e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm
    have hac_pos := algebraicConnectivity_pos G hconn hV
    suffices ∀ k : V, ev k = 0 → e k = ⟨Fintype.card V - 1, by omega⟩ by
      exact e.injective ((this i hi).trans (this j₀ hj₀).symm)
    intro k hk
    ext; simp only [Fin.val_mk]
    by_contra hne
    have hle : (e k).val ≤ Fintype.card V - 2 := by omega
    have hge : hLH.eigenvalues₀ (e k) ≥ hLH.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ :=
      hLH.eigenvalues₀_antitone (Fin.le_def.mpr (by simp; exact hle))
    have hk' : hLH.eigenvalues₀ (e k) = 0 := by
      simp [Matrix.IsHermitian.eigenvalues] at hk; exact hk
    have hac_eq : algebraicConnectivity G hV =
        hLH.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ := rfl
    linarith
  -- For i ≠ j₀: ev i ≥ ac
  have hevi_bound : ∀ i ∈ Finset.univ.erase j₀,
      algebraicConnectivity G hV ≤ ev i := by
    intro i hi
    have hne : i ≠ j₀ := Finset.ne_of_mem_erase hi
    by_contra hlt; push_neg at hlt
    have hnn : (0 : ℝ) ≤ ev i := (SimpleGraph.posSemidef_lapMatrix ℝ G).eigenvalues_nonneg i
    set e := (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card V))).symm
    have hidx : (e i).val ≥ Fintype.card V - 1 := by
      by_contra h; push_neg at h
      have hle2 : e i ≤ ⟨Fintype.card V - 2, by omega⟩ := by simp [Fin.le_def]; omega
      exact absurd (hLH.eigenvalues₀_antitone hle2) (not_le.mpr hlt)
    have heq : e i = ⟨Fintype.card V - 1, by omega⟩ := by
      ext; simp only [Fin.val_mk]; omega
    have hev0 : ev i = 0 := by
      show hLH.eigenvalues₀ (e i) = 0
      rw [heq]; apply le_antisymm _ (heq ▸ hnn)
      have hdet : (G.lapMatrix ℝ).det = 0 := SimpleGraph.det_lapMatrix_eq_zero G
      rw [hLH.det_eq_prod_eigenvalues] at hdet
      obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp
        (show ∏ j : V, hLH.eigenvalues j = 0 from by exact_mod_cast hdet)
      have hej : hLH.eigenvalues₀ (e j) = 0 := by
        simp [Matrix.IsHermitian.eigenvalues] at hj; exact hj
      have hfin_le : e j ≤ ⟨Fintype.card V - 1, by omega⟩ := by
        simp only [Fin.le_def, Fin.val_mk]; omega
      have : hLH.eigenvalues₀ ⟨Fintype.card V - 1, by omega⟩ ≤ hLH.eigenvalues₀ (e j) :=
        hLH.eigenvalues₀_antitone hfin_le
      linarith
    exact hne (huniq i hev0)
  -- Final inequality: ac * d(n-d) ≤ ∑ ev i * (d - ev i)²
  have hgoal_eq : algebraicConnectivity G hV * ((d : ℝ) * ((Fintype.card V : ℝ) - (d : ℝ))) =
      algebraicConnectivity G hV *
        (∑ i : V, ((d : ℝ) - ev i) ^ 2 - (d : ℝ) ^ 2) := by
    rw [hA2_trace]; ring
  have hB := Finset.add_sum_erase Finset.univ
    (fun i : V => ((d : ℝ) - ev i) ^ 2) (Finset.mem_univ j₀)
  have hBval : (fun i : V => ((d : ℝ) - ev i) ^ 2) j₀ = (d : ℝ) ^ 2 := by
    show ((d : ℝ) - ev j₀) ^ 2 = _; rw [hj₀, sub_zero]
  rw [hBval] at hB
  have hC : algebraicConnectivity G hV *
      (Finset.univ.erase j₀).sum (fun i : V => ((d : ℝ) - ev i) ^ 2) ≤
      (Finset.univ.erase j₀).sum (fun i : V => ev i * ((d : ℝ) - ev i) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hevi_bound i hi) (sq_nonneg _)
  have hD := Finset.add_sum_erase Finset.univ
    (fun i : V => ev i * ((d : ℝ) - ev i) ^ 2) (Finset.mem_univ j₀)
  have hDval : (fun i : V => ev i * ((d : ℝ) - ev i) ^ 2) j₀ = 0 := by
    show ev j₀ * ((d : ℝ) - ev j₀) ^ 2 = _; rw [hj₀]; ring
  rw [hDval, zero_add] at hD
  rw [hgoal_eq]
  have hB' : ∑ i : V, ((d : ℝ) - ev i) ^ 2 - (d : ℝ) ^ 2 =
      (Finset.univ.erase j₀).sum (fun i : V => ((d : ℝ) - ev i) ^ 2) := by
    linarith [hB.symm]
  rw [hB']
  have hD' : ∑ i : V, ev i * ((d : ℝ) - ev i) ^ 2 =
      (Finset.univ.erase j₀).sum (fun i : V => ev i * ((d : ℝ) - ev i) ^ 2) := hD.symm
  linarith

/-- Computation rule for `edgeLift`: on a concrete edge s(u,v), the lift is f(u) + f(v). -/
@[simp]
lemma edgeLift_mk {R : Type*} [AddCommMonoid R] (f : V → R)
    {u v : V} (h : s(u, v) ∈ G.edgeSet) :
    edgeLift G f ⟨s(u, v), h⟩ = f u + f v := by
  simp [edgeLift, Sym2.lift_mk]

/-- When two edges are adjacent in T(G), they share a vertex u with
e₁ = s(u,v) and e₂ = s(u,w), so the edgeLift difference squares to a vertex difference. -/
lemma edgeLift_triangleAdj_sq (f : V → ℝ) (e₁ e₂ : G.edgeSet)
    (hadj : (triangleGraph G).Adj e₁ e₂) :
    ∃ v w : V, G.Adj v w ∧
      (edgeLift G f e₁ - edgeLift G f e₂) ^ 2 = (f v - f w) ^ 2 := by
  obtain ⟨u, v, w, h1, h2, hvw⟩ := hadj
  refine ⟨v, w, hvw, ?_⟩
  -- e₁.val = s(u,v) and e₂.val = s(u,w)
  have he1 : edgeLift G f e₁ = f u + f v := by
    change Sym2.lift ⟨fun a b => f a + f b, _⟩ e₁.val = _
    rw [h1, Sym2.lift_mk]
  have he2 : edgeLift G f e₂ = f u + f w := by
    change Sym2.lift ⟨fun a b => f a + f b, _⟩ e₂.val = _
    rw [h2, Sym2.lift_mk]
  rw [he1, he2]; ring

/-- For d-regular graphs, the sum of edgeLift equals d times the sum of f.
Each vertex appears in exactly d edges, so ∑ₑ (f(u)+f(v)) = d · ∑ᵥ f(v). -/
lemma edgeLift_sum_regular (f : V → ℝ) (d : ℕ) (hreg : G.IsRegularOfDegree d) :
    ∑ e : G.edgeSet, edgeLift G f e = (d : ℝ) * ∑ v : V, f v := by
  classical
  -- Strategy: ∑_e (fu+fv) = (∑_i ∑_j [Adj i j] (fi+fj)) / 2 = (2d·∑f) / 2 = d·∑f
  -- Step 1: double sum = 2d · ∑f
  have hdouble : ∑ i : V, ∑ j : V,
      (if G.Adj i j then f i + f j else (0 : ℝ)) = 2 * (d : ℝ) * ∑ v, f v := by
    simp_rw [show ∀ (i j : V), (if G.Adj i j then f i + f j else (0 : ℝ)) =
      (if G.Adj i j then f i else 0) + (if G.Adj i j then f j else 0) from
      fun i j => by split_ifs <;> simp]
    simp_rw [Finset.sum_add_distrib]
    -- Part A: ∑_i ∑_j [Adj i j] fi = d · ∑f
    have hA : ∑ i : V, ∑ j : V, (if G.Adj i j then f i else (0 : ℝ)) =
        (d : ℝ) * ∑ v, f v := by
      simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      simp_rw [show ∀ i : V, ((Finset.univ.filter (G.Adj i)).card : ℝ) = (d : ℝ) from
        fun i => by
          rw [show Finset.univ.filter (G.Adj i) = G.neighborFinset i from
            (SimpleGraph.neighborFinset_eq_filter G).symm]
          exact_mod_cast hreg.degree_eq i]
      rw [← Finset.mul_sum]
    -- Part B: ∑_i ∑_j [Adj i j] fj = d · ∑f (swap sums, then adj_comm gives hA)
    have hB : ∑ i : V, ∑ j : V, (if G.Adj i j then f j else (0 : ℝ)) =
        (d : ℝ) * ∑ v, f v := by
      have hswap : ∀ (a b : V), (if G.Adj b a then f a else (0 : ℝ)) =
          (if G.Adj a b then f a else 0) := by
        intro a b; congr 1; exact propext (G.adj_comm b a)
      rw [Finset.sum_comm]; simp_rw [hswap]; exact hA
    linarith
  -- Step 2: edge sum = double sum / 2 (via dart decomposition)
  suffices hedge : (∑ e : G.edgeSet, edgeLift G f e) * 2 =
      ∑ i : V, ∑ j : V, if G.Adj i j then f i + f j else (0 : ℝ) by
    linarith
  -- Convert to dart sum, then to double vertex sum
  -- h1: double vertex sum = dart sum (reusing pattern from quadratic_form_eq_edge_sum)
  have h1 : ∑ i : V, ∑ j : V,
      (if G.Adj i j then f i + f j else (0 : ℝ)) =
      ∑ a : G.Dart, (f a.toProd.1 + f a.toProd.2) := by
    symm; simp_rw [← Finset.sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun (a : G.Dart) => a.toProd.1)
        (f := fun a => f a.toProd.1 + f a.toProd.2)
        (fun _ _ => Finset.mem_univ _)]
    congr 1 with v
    rw [G.dart_fst_fiber v, Finset.sum_image
      (fun _ _ _ _ h => G.dartOfNeighborSet_injective v h)]
    simp only [SimpleGraph.dartOfNeighborSet,
      SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter,
      SimpleGraph.mem_neighborSet]
    conv_rhs => rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (G.Adj v))
      (fun w => by simp [SimpleGraph.mem_neighborSet])
      (fun w => f v + f w)).symm
  -- h2: dart sum = 2 * edge finset sum
  have h2 : ∑ a : G.Dart, (f a.toProd.1 + f a.toProd.2) =
      2 * ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => f u + f v, fun u v => add_comm _ _⟩ e := by
    rw [Finset.mul_sum, ← Finset.sum_fiberwise_of_maps_to
      (g := fun (a : G.Dart) => a.edge) (s := Finset.univ)
      (t := G.edgeFinset) (fun a _ => SimpleGraph.mem_edgeFinset.mpr a.edge_mem)]
    apply Finset.sum_congr rfl; intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      set d₀ : G.Dart := ⟨(u, v), hadj⟩
      rw [show Finset.univ.filter (fun a : G.Dart => a.edge = s(u, v)) =
        {d₀, d₀.symm} from by
          ext d'; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton]
          exact SimpleGraph.dart_edge_eq_iff d' d₀]
      rw [Finset.sum_insert (show d₀ ∉ ({d₀.symm} : Finset _) from by
        simp only [Finset.mem_singleton]; exact d₀.symm_ne.symm),
        Finset.sum_singleton]
      simp only [Sym2.lift_mk, d₀, SimpleGraph.Dart.symm, Prod.swap]; ring
  -- h3: edge finset sum = edgeSet subtype sum
  have h3 : ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => f u + f v, fun u v => add_comm _ _⟩ e =
      ∑ e : G.edgeSet, edgeLift G f e := by
    simp only [edgeLift]
    rw [← Finset.sum_coe_sort]
    exact @Fintype.sum_equiv _ _ ℝ _ _ _
      (Equiv.subtypeEquivRight (fun _ => SimpleGraph.mem_edgeFinset (G := G)))
      _ _ (fun _ => rfl)
  linarith [h1, h2, h3]

/-- For d-regular G with ∑ f = 0, the edgeLift sum vanishes. -/
lemma edgeLift_sum_zero (f : V → ℝ) (d : ℕ) (hreg : G.IsRegularOfDegree d)
    (hfsum : ∑ v, f v = 0) :
    ∑ e : G.edgeSet, edgeLift G f e = 0 := by
  rw [edgeLift_sum_regular G f d hreg, hfsum, mul_zero]

/-- Norm squared of edgeLift for d-regular graphs:
∑ₑ (f(u)+f(v))² = d · ∑ᵥ f(v)² + 2 · ∑ₑ f(u)·f(v).
Expands (f u + f v)² = f u² + f v² + 2·f u·f v, then uses double-counting
for the squared terms (each vertex in d edges) and keeps cross terms as edge sum. -/
lemma edgeLift_norm_sq (f : V → ℝ) (d : ℕ) (hreg : G.IsRegularOfDegree d) :
    ∑ e : G.edgeSet, (edgeLift G f e) ^ 2 =
    (d : ℝ) * ∑ v, (f v) ^ 2 + 2 * ∑ e : G.edgeSet,
      Sym2.lift ⟨fun u v => f u * f v, fun u v => by ring⟩ e.val := by
  -- (fu+fv)² = fu² + fv² + 2·fu·fv
  -- ∑ₑ (fu+fv)² = ∑ₑ (fu² + fv²) + 2·∑ₑ fu·fv
  -- ∑ₑ (fu² + fv²) = d·∑ᵥ fv² (same double-counting as edgeLift_sum_regular)
  have hsq : ∀ e : G.edgeSet, (edgeLift G f e) ^ 2 =
      edgeLift G (fun v => (f v) ^ 2) e +
      2 * Sym2.lift ⟨fun u v => f u * f v, fun u v => by ring⟩ e.val := by
    intro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      simp only [edgeLift_mk, Sym2.lift_mk]
      ring
  simp_rw [hsq, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  exact edgeLift_sum_regular G (fun v => (f v) ^ 2) d hreg

-- The T(G)-Laplacian quadratic form applied to edgeLift f decomposes as a sum
-- over directed triangles. Each T(G)-adjacent ordered pair (e₁,e₂) corresponds
-- bijectively to an ordered triple (u,v,w) with Adj u v, Adj u w, Adj v w,
-- where e₁ = s(u,v), e₂ = s(u,w), and (edgeLift f e₁ - edgeLift f e₂)² = (f v - f w)².
section QuadraticForm
attribute [local instance] Classical.propDecidable

lemma triangleGraph_quadratic_form (f : V → ℝ) :
    (∑ e₁ : G.edgeSet, ∑ e₂ : G.edgeSet,
      if (triangleGraph G).Adj e₁ e₂
      then (edgeLift G f e₁ - edgeLift G f e₂) ^ 2
      else (0 : ℝ)) =
    ∑ u : V, ∑ v : V, ∑ w : V,
      if G.Adj u v ∧ G.Adj u w ∧ G.Adj v w
      then (f v - f w) ^ 2
      else (0 : ℝ) := by
  -- Define flat filtered finsets for both sides
  set adjPairs := (Finset.univ : Finset (G.edgeSet × G.edgeSet)).filter
    (fun p => (triangleGraph G).Adj p.1 p.2) with adjPairs_def
  set dirTri := (Finset.univ : Finset (V × V × V)).filter
    (fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2) with dirTri_def
  -- Rewrite LHS as sum over adjPairs
  have hLHS : (∑ e₁ : G.edgeSet, ∑ e₂ : G.edgeSet,
      if (triangleGraph G).Adj e₁ e₂
      then (edgeLift G f e₁ - edgeLift G f e₂) ^ 2 else (0 : ℝ)) =
      adjPairs.sum (fun p => (edgeLift G f p.1 - edgeLift G f p.2) ^ 2) := by
    simp only [adjPairs_def]
    rw [← Finset.univ_product_univ, Finset.sum_filter, ← Finset.sum_product']
  -- Rewrite RHS as sum over dirTri
  have hRHS : (∑ u : V, ∑ v : V, ∑ w : V,
      if G.Adj u v ∧ G.Adj u w ∧ G.Adj v w
      then (f v - f w) ^ 2 else (0 : ℝ)) =
      dirTri.sum (fun t => (f t.2.1 - f t.2.2) ^ 2) := by
    simp only [dirTri_def]
    -- First flatten ∑ v ∑ w to ∑ (v,w), then ∑ u ∑ (v,w) to ∑ (u,(v,w))
    simp_rw [show ∀ u : V, (∑ v : V, ∑ w : V,
        if G.Adj u v ∧ G.Adj u w ∧ G.Adj v w then (f v - f w) ^ 2 else (0 : ℝ)) =
      ∑ vw : V × V, if G.Adj u vw.1 ∧ G.Adj u vw.2 ∧ G.Adj vw.1 vw.2
        then (f vw.1 - f vw.2) ^ 2 else 0 from fun u =>
      (Fintype.sum_prod_type' (fun v w =>
        if G.Adj u v ∧ G.Adj u w ∧ G.Adj v w then (f v - f w) ^ 2 else 0)).symm]
    rw [(Fintype.sum_prod_type' (fun u (vw : V × V) =>
        if G.Adj u vw.1 ∧ G.Adj u vw.2 ∧ G.Adj vw.1 vw.2
        then (f vw.1 - f vw.2) ^ 2 else (0 : ℝ))).symm,
      ← Finset.sum_filter]
  rw [hLHS, hRHS]
  -- Apply sum_bij: dirTri → adjPairs
  symm
  apply Finset.sum_bij
    (fun (t : V × V × V) (ht : t ∈ dirTri) =>
      have h := (Finset.mem_filter.mp ht).2
      ((⟨s(t.1, t.2.1), G.mem_edgeSet.mpr h.1⟩,
        ⟨s(t.1, t.2.2), G.mem_edgeSet.mpr h.2.1⟩) : G.edgeSet × G.edgeSet))
  · -- hi: image lands in adjPairs
    intro ⟨u, v, w⟩ ht
    simp only [adjPairs_def, Finset.mem_filter, Finset.mem_univ, true_and]
    have h := (Finset.mem_filter.mp ht).2
    exact ⟨u, v, w, rfl, rfl, h.2.2⟩
  · -- i_inj: injective (Sym2.eq_iff case analysis)
    intro ⟨u₁, v₁, w₁⟩ ht₁ ⟨u₂, v₂, w₂⟩ ht₂ heq
    have h₁ := (Finset.mem_filter.mp ht₁).2
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at heq
    obtain ⟨he1, he2⟩ := heq
    rw [Sym2.eq_iff] at he1 he2
    -- 4 cases from Sym2.eq_iff on each equation
    rcases he1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- u₁=u₂, v₁=v₂
      rcases he2 with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · -- u₁=w₂, w₁=u₁ → w₁=u₁, contradicts Adj u₁ w₁
        exfalso; exact h₁.2.1.ne rfl
    · rcases he2 with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
      · exact absurd rfl h₁.1.ne
      · exact absurd rfl h₁.2.2.ne
  · -- i_surj: surjective (extract the shared vertex from T(G)-adjacency)
    intro ⟨e₁, e₂⟩ hp
    have hp' := (Finset.mem_filter.mp hp).2
    obtain ⟨u, v, w, h1, h2, hvw⟩ := hp'
    have huv : G.Adj u v := G.mem_edgeSet.mp (h1 ▸ e₁.2)
    have huw : G.Adj u w := G.mem_edgeSet.mp (h2 ▸ e₂.2)
    refine ⟨⟨u, v, w⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv, huw, hvw⟩,
      Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)⟩
  · -- h: value equality (edgeLift_mk + ring)
    intro ⟨u, v, w⟩ ht
    have h := (Finset.mem_filter.mp ht).2
    simp only [edgeLift_mk, G.mem_edgeSet.mpr h.1, G.mem_edgeSet.mpr h.2.1]
    ring

/-- The T(G)-quadratic form of edgeLift f is bounded by 2(d-1) times the G-quadratic form.
Each edge {v,w} participates in at most d-1 triangles (common neighbors ⊆ N(v)\{w}). -/
lemma triangleGraph_quadratic_bound (f : V → ℝ) (d : ℕ) (hreg : G.IsRegularOfDegree d) :
    (∑ e₁ : G.edgeSet, ∑ e₂ : G.edgeSet,
      if (triangleGraph G).Adj e₁ e₂
      then (edgeLift G f e₁ - edgeLift G f e₂) ^ 2
      else (0 : ℝ)) ≤
    2 * (d - 1 : ℝ) * ∑ e : G.edgeSet,
      Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val := by
  -- Step 1: Rewrite LHS using triangleGraph_quadratic_form
  rw [triangleGraph_quadratic_form]
  -- Goal: ∑ u v w, [Adj∧Adj∧Adj] (fv-fw)² ≤ 2(d-1) · ∑ₑ (fu-fv)²
  -- Step 2: Swap sums to group by (v,w) — the "edge" being counted
  -- ∑ u v w, [u∈N(v)∩N(w)∧Adj v w] (fv-fw)² = ∑ v w, |N(v)∩N(w)∩{u|Adj v w}| · (fv-fw)²
  -- = ∑ v w, [Adj v w] · |{u : Adj u v ∧ Adj u w}| · (fv-fw)²
  -- Step 3: Bound |{u : Adj u v ∧ Adj u w}| ≤ d-1 for each edge {v,w}
  -- Step 4: So LHS ≤ ∑ v w, [Adj v w] · (d-1) · (fv-fw)² = (d-1) · ∑ₑ 2·(fv-fw)²
  -- (factor 2 from ordered vs unordered)
  -- Convert ∑ u v w to ∑ v w (∑ u [Adj u v ∧ Adj u w]) · [Adj v w] · (fv-fw)²
  -- Step 2: Key bound on common neighbor count
  -- |{u | Adj u v ∧ Adj u w ∧ Adj v w}| ≤ d-1 (⊆ N(v)\{w} when Adj v w, empty otherwise)
  have hcount : ∀ v w : V, (Finset.univ.filter
      (fun u => G.Adj u v ∧ G.Adj u w ∧ G.Adj v w)).card ≤ d - 1 := by
    intro v w
    by_cases hvw : G.Adj v w
    · have : Finset.univ.filter (fun u => G.Adj u v ∧ G.Adj u w ∧ G.Adj v w) =
          Finset.univ.filter (fun u => G.Adj u v ∧ G.Adj u w) := by ext u; simp [hvw]
      rw [this]
      have hsub : Finset.univ.filter (fun u => G.Adj u v ∧ G.Adj u w) ⊆
          (G.neighborFinset v).erase w := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · intro heq; subst heq; exact hu.2.ne rfl  -- u=w → Adj w w, impossible
        · rw [SimpleGraph.mem_neighborFinset]; exact hu.1.symm
      have hmem_w : w ∈ G.neighborFinset v := by
        rw [SimpleGraph.mem_neighborFinset]; exact hvw
      linarith [Finset.card_le_card hsub,
        show ((G.neighborFinset v).erase w).card = d - 1 from by
          rw [Finset.card_erase_of_mem hmem_w]
          show (G.neighborFinset v).card - 1 = d - 1
          rw [show (G.neighborFinset v).card = d from hreg.degree_eq v]]
    · convert Nat.zero_le _
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun u _ h => hvw h.2.2
  -- Commute sums: ∑ u v w → ∑ v w u, then factor (fv-fw)² out of u-sum
  rw [Finset.sum_comm (f := fun u v => _)]
  conv_lhs => arg 2; ext v; rw [Finset.sum_comm (f := fun u w => _)]
  -- Now: ∑ v w u, [Adj u v ∧ Adj u w ∧ Adj v w] (fv-fw)²
  -- Factor: ∑ u [P(u)] c = |filter| · c (c = (fv-fw)² doesn't depend on u)
  conv_lhs => arg 2; ext v; arg 2; ext w
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- Per-term bound: |filter| · c ≤ [Adj v w] · (d-1) · c
  -- When Adj v w: |filter| ≤ d-1 by hcount
  -- When ¬Adj v w: |filter| = 0 (Adj v w is part of the conjunction)
  -- Dart→edge: ∑ v w [Adj v w] g(v,w) = 2 · ∑ₑ g(e)
  have hdart_edge : ∑ v : V, ∑ w : V,
      (if G.Adj v w then (f v - f w) ^ 2 else (0 : ℝ)) =
      2 * ∑ e : G.edgeSet,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val := by
    have hqf := quadratic_form_eq_edge_sum G f
    rw [SimpleGraph.lapMatrix_toLinearMap₂'] at hqf
    -- Convert edgeFinset sum to edgeSet sum (same as h3 in edgeLift_sum_regular)
    have h3 : ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e =
        ∑ e : G.edgeSet,
          Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val := by
      rw [← Finset.sum_coe_sort]
      exact @Fintype.sum_equiv _ _ ℝ _ _ _
        (Equiv.subtypeEquivRight (fun _ => SimpleGraph.mem_edgeFinset (G := G)))
        _ _ (fun _ => rfl)
    linarith
  calc ∑ v : V, ∑ w : V,
        ↑(Finset.univ.filter (fun u => G.Adj u v ∧ G.Adj u w ∧ G.Adj v w)).card *
          (f v - f w) ^ 2
      ≤ ∑ v : V, ∑ w : V,
          if G.Adj v w then ((d : ℝ) - 1) * (f v - f w) ^ 2 else 0 := by
        apply Finset.sum_le_sum; intro v _
        apply Finset.sum_le_sum; intro w _
        by_cases hvw : G.Adj v w
        · rw [if_pos hvw]
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          have hd_pos : 1 ≤ d := by
            rw [← hreg.degree_eq v]
            exact Finset.card_pos.mpr ⟨w, by rw [SimpleGraph.mem_neighborFinset]; exact hvw⟩
          calc (↑(Finset.univ.filter _).card : ℝ) ≤ ↑(d - 1) := by
                exact_mod_cast hcount v w
            _ = (d : ℝ) - 1 := by push_cast [Nat.cast_sub hd_pos]; ring
        · -- ¬Adj v w: filter empty, LHS = 0
          have : (Finset.univ.filter (fun u => G.Adj u v ∧ G.Adj u w ∧ G.Adj v w)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            exact fun u _ h => hvw h.2.2
          simp [this, hvw]
    _ = ((d : ℝ) - 1) * ∑ v : V, ∑ w : V,
          if G.Adj v w then (f v - f w) ^ 2 else (0 : ℝ) := by
        rw [Finset.mul_sum]; congr 1; ext v
        rw [Finset.mul_sum]; congr 1; ext w
        split_ifs <;> ring
    _ = 2 * ((d : ℝ) - 1) * ∑ e : G.edgeSet,
          Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val := by
        rw [hdart_edge]; ring

/-- The norm squared of edgeLift f for a Fiedler-like vector:
‖h‖² = (2d - λ₂) · ‖f‖², using (fu+fv)² + (fu-fv)² = 2(fu²+fv²). -/
lemma edgeLift_norm_fiedler (f : V → ℝ) (d : ℕ) (hreg : G.IsRegularOfDegree d)
    (hV : Fintype.card V ≥ 2)
    (hf_eigen : ∑ e : G.edgeSet,
      Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val =
      algebraicConnectivity G hV * ∑ v, (f v) ^ 2) :
    ∑ e : G.edgeSet, (edgeLift G f e) ^ 2 =
    (2 * (d : ℝ) - algebraicConnectivity G hV) * ∑ v, (f v) ^ 2 := by
  -- edgeLift_norm_sq: ∑ (fu+fv)² = d·∑fv² + 2·∑_e fu·fv
  rw [edgeLift_norm_sq G f d hreg]
  -- Need: d·∑fv² + 2·∑_e fu·fv = (2d - ac)·∑fv²
  -- i.e., 2·∑_e fu·fv = (d - ac)·∑fv²
  -- From: ∑_e (fu-fv)² = ∑_e (fu²+fv²) - 2·∑_e fu·fv = d·∑fv² - 2·∑_e fu·fv
  -- So 2·∑_e fu·fv = d·∑fv² - ∑_e (fu-fv)² = d·∑fv² - ac·∑fv² = (d-ac)·∑fv²
  -- Use: ∑_e (fu²+fv²) = d·∑fv² (same double-counting as edgeLift_sum_regular)
  have hsq_sum : ∑ e : G.edgeSet,
      Sym2.lift ⟨fun u v => (f u) ^ 2 + (f v) ^ 2, fun u v => by ring⟩ e.val =
      (d : ℝ) * ∑ v, (f v) ^ 2 := by
    have := edgeLift_sum_regular G (fun v => (f v) ^ 2) d hreg
    simp only [edgeLift] at this
    convert this using 1
  -- ∑_e (fu-fv)² = ∑_e (fu²+fv²) - 2·∑_e fu·fv
  have hexpand : ∀ e : G.edgeSet,
      Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val =
      Sym2.lift ⟨fun u v => (f u) ^ 2 + (f v) ^ 2, fun u v => by ring⟩ e.val -
      2 * Sym2.lift ⟨fun u v => f u * f v, fun u v => by ring⟩ e.val := by
    intro ⟨e, he⟩
    induction e using Sym2.ind with | _ u v => simp [Sym2.lift_mk]; ring
  have henergy : ∑ e : G.edgeSet,
      Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val =
      (d : ℝ) * ∑ v, (f v) ^ 2 -
      2 * ∑ e : G.edgeSet,
        Sym2.lift ⟨fun u v => f u * f v, fun u v => by ring⟩ e.val := by
    simp_rw [hexpand, Finset.sum_sub_distrib, ← Finset.mul_sum, hsq_sum]
  -- Combine: 2·cross = d·∑fv² - energy = d·∑fv² - ac·∑fv²
  linarith [hf_eigen, henergy]

end QuadraticForm

/-- **Paper 13**: For d-regular graphs, the algebraic connectivity of the triangle graph
T(G) is at most the algebraic connectivity of G.
  λ₂(T(G)) ≤ λ₂(G)

Proof sketch (Rayleigh quotient bridge):
1. Take the Fiedler vector f : V → ℝ of G (eigenvector for λ₂, with ∑ f = 0).
2. Lift to h := edgeLift G f : G.edgeSet → ℝ, i.e. h({u,v}) = f(u) + f(v).
3. For d-regular G: ∑ₑ h(e) = ∑_{e={u,v}} (f(u)+f(v)) = d · ∑ᵥ f(v) = 0.
4. Rayleigh quotient: λ₂(T(G)) ≤ hᵀ L_{T(G)} h / ‖h‖².
5. Key quadratic form identity:
   hᵀ L_{T(G)} h = ∑_{triangles {u,v,w}} [(f(v)-f(w))² + (f(u)-f(w))² + (f(u)-f(v))²]
   ≤ tri_max · ∑_{e={u,v}∈E} (f(u)-f(v))² = tri_max · fᵀ L_G f
6. Norm bound: ‖h‖² ≥ C(d) · ‖f‖² for suitable C(d).
7. Combine: λ₂(T(G)) ≤ (tri_max/C(d)) · fᵀ L_G f / ‖f‖² = (tri_max/C(d)) · λ₂(G).
   For d-regular graphs, tri_max/C(d) ≤ 1 gives the result.

This requires Laplacian quadratic form decomposition on T(G), which needs
triangle enumeration and adjacency structure not yet available in Mathlib. -/
theorem lambda2_triangle_graph_le
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (d : ℕ) (hreg : G.IsRegularOfDegree d)
    (hV' : Fintype.card G.edgeSet ≥ 2)
    (hTconn : (triangleGraph G).Connected) :
    algebraicConnectivity (triangleGraph G) hV' ≤ algebraicConnectivity G hV := by
  -- Step 1: Get Fiedler vector f for G
  obtain ⟨f, hf_ne, hf_sum, hf_eig⟩ := fiedler_vector_exists G hconn hV
  -- Step 2: Define h = edgeLift G f, show ∑ h = 0
  set h := edgeLift G f with hh_def
  have hh_sum : ∑ e : G.edgeSet, h e = 0 :=
    edgeLift_sum_zero G f d hreg hf_sum
  -- Step 3: Energy identity: ∑_e (fu-fv)² = ac · ‖f‖²
  have hf_edge_energy : ∑ e : G.edgeSet,
      Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val =
      algebraicConnectivity G hV * ∑ v, (f v) ^ 2 := by
    -- fᵀLf = ac·‖f‖² from eigenvector property
    have heig : dotProduct f ((G.lapMatrix ℝ).mulVec f) =
        algebraicConnectivity G hV * dotProduct f f := by
      rw [hf_eig]; simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_comm (f _) (algebraicConnectivity G hV * f _),
        show ∀ x, algebraicConnectivity G hV * f x * f x = f x ^ 2 * algebraicConnectivity G hV
          from fun x => by ring]
      rw [← Finset.sum_mul]; ring
    -- fᵀLf = ∑_e (fu-fv)² from quadratic_form_eq_edge_sum
    have hqf := quadratic_form_eq_edge_sum G f
    -- Connect: need toLinearMap₂' = dotProduct form
    have hlm : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f =
        dotProduct f ((G.lapMatrix ℝ).mulVec f) := by
      rw [Matrix.toLinearMap₂'_apply']
    rw [hlm, heig] at hqf
    -- hqf: ac * ‖f‖² = ∑_e∈edgeFinset (fu-fv)²
    -- Convert edgeFinset → edgeSet
    have hconv : ∑ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e =
        ∑ e : G.edgeSet,
          Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val := by
      rw [← Finset.sum_coe_sort]
      exact @Fintype.sum_equiv _ _ ℝ _ _ _
        (Equiv.subtypeEquivRight (fun _ => SimpleGraph.mem_edgeFinset (G := G)))
        _ _ (fun _ => rfl)
    have hdot : dotProduct f f = ∑ v, (f v) ^ 2 := by
      simp [dotProduct, sq]
    rw [hdot] at hqf; linarith [hconv]
  -- Step 4: Norm of h = (2d - ac) · ‖f‖²
  have hh_norm : ∑ e : G.edgeSet, (h e) ^ 2 =
      (2 * (d : ℝ) - algebraicConnectivity G hV) * ∑ v, (f v) ^ 2 :=
    edgeLift_norm_fiedler G f d hreg hV hf_edge_energy
  -- Step 5: Positivity of ‖f‖²
  have hf_sq_pos : 0 < ∑ v, (f v) ^ 2 := by
    apply Finset.sum_pos' (fun i _ => sq_nonneg (f i))
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra h; push_neg at h; exact hf_ne (funext h)
    exact ⟨v, Finset.mem_univ _, by positivity⟩
  -- Step 6: ac(G) > 0
  have hac_pos := algebraicConnectivity_pos G hconn hV
  -- Step 7: The full Rayleigh quotient argument
  -- ac(T(G)) ≤ hᵀ L_{T(G)} h / ‖h‖²
  -- hᵀ L_{T(G)} h = (indicator sum) / 2
  -- ≤ 2(d-1) · Energy / 2 = (d-1) · ac · ‖f‖²
  -- ‖h‖² = (2d-ac) · ‖f‖²
  -- So ac(T(G)) ≤ (d-1)·ac / (2d-ac) ≤ ac  (when ac ≤ d+1)
  -- This requires connecting the Rayleigh quotient API with the indicator sums.
  sorry

end Topostability
