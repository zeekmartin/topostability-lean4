import Topostability.Defs
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Sort

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Laplacian matrix of a simple graph over ℝ is Hermitian (symmetric). -/
lemma isHermitian_lapMatrix : (G.lapMatrix ℝ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact G.isSymm_lapMatrix (R := ℝ)

/-- The algebraic connectivity of `G` is the second smallest eigenvalue of the
Laplacian matrix. This requires at least 2 vertices. Since `eigenvalues₀` is
antitone, index `card V - 2` is the second smallest. -/
noncomputable def algebraicConnectivity (hV : Fintype.card V ≥ 2) : ℝ :=
  (isHermitian_lapMatrix G).eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩

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
              (G.isSymm_lapMatrix (R := ℝ)).apply j i]
        simpa [Matrix.mulVec, dotProduct] using congr_fun h1 j]
      simp [dotProduct]]
  · -- (c) L *ᵥ f = ac • f: from mulVec_eigenvectorBasis
    have := hL.mulVec_eigenvectorBasis idx
    -- eigenvalues idx = ac by definition; ⇑(B idx) = (B idx).ofLp
    convert this using 2
    simp [idx, algebraicConnectivity, Matrix.IsHermitian.eigenvalues]

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

end Topostability
