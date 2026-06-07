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

/-- The algebraic connectivity (second-smallest Laplacian eigenvalue) is nonnegative,
because the graph Laplacian is positive semidefinite. -/
lemma algebraicConnectivity_nonneg (hV : Fintype.card V ≥ 2) :
    0 ≤ algebraicConnectivity G hV := by
  unfold algebraicConnectivity
  have h := (SimpleGraph.posSemidef_lapMatrix ℝ G).eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨Fintype.card V - 2, by omega⟩)
  convert h using 1
  simp [Matrix.IsHermitian.eigenvalues]

/-- **Conjecture 1** (Paper 11): For every connected graph `G` on at least 2 vertices,
`tauG G ≤ algebraicConnectivity G`. -/
theorem conjecture_tauG_le_algebraicConnectivity
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2) :
    (tauG G : ℝ) ≤ algebraicConnectivity G hV := by
  rcases Nat.eq_zero_or_pos (tauG G) with h0 | hpos
  · -- Sub-case `tauG G = 0`: the bound reduces to `0 ≤ λ₂`, which holds because
    -- the Laplacian is positive semidefinite. Covers all triangle-free graphs.
    rw [h0, Nat.cast_zero]
    exact algebraicConnectivity_nonneg G hV
  · -- Sub-case `tauG G ≥ 1`: the genuine spectral content of the conjecture.
    sorry

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

end Topostability
