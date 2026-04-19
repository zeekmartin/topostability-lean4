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
    (hd : 2 ≤ d)
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
  -- Key spectral bound: ac ≤ d for d-regular connected graphs
  -- Proof: use test vector x = 1_v - 1_w for any edge {v,w}. Then ∑x = 0,
  -- xᵀLx = degree(v) + degree(w) - 2·A_{vw} = 2d-2, ‖x‖² = 2.
  -- Rayleigh: ac ≤ (2d-2)/2 = d-1 < d. (Actually ac ≤ n·d/(n-1) in general.)
  -- ac ≤ d+1 for d-regular connected graphs (Rayleigh with x = 1_u - 1_v)
  have hac_le_dp1_early : algebraicConnectivity G hV ≤ (d : ℝ) + 1 := by
    -- Get an edge from d ≥ 2 + regularity
    set u₀ := hconn.nonempty.some
    have ⟨w₀, hw₀⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset u₀).card from by
      have := hreg.degree_eq u₀; simp only [SimpleGraph.degree] at this; omega)
    have huv : G.Adj u₀ w₀ := by rwa [SimpleGraph.mem_neighborFinset] at hw₀
    -- Test vector: x = 1_u - 1_v (as difference of indicators)
    set u := u₀; set v := w₀
    set x : V → ℝ := fun w => (if w = u then 1 else 0) - (if w = v then 1 else 0)
    have hxne : x ≠ 0 := by
      intro h; have := congr_fun h u; simp [x, huv.ne] at this
    have hxsum : ∑ w, x w = 0 := by
      simp only [x, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      norm_num
    have hray := algebraicConnectivity_le_rayleigh G hconn hV x hxne hxsum
    -- ‖x‖² = 1² + (-1)² = 2 (u and v contribute, rest 0)
    have hxx : ∑ w, (x w) ^ 2 = 2 := by
      -- Extract u and v from the sum
      have hvu : v ≠ u := huv.ne.symm
      rw [show ∑ w, (x w) ^ 2 = (x u) ^ 2 + (x v) ^ 2 +
          ∑ w ∈ (Finset.univ.erase u).erase v, (x w) ^ 2 from by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hvu, Finset.mem_univ v⟩)]
        ring]
      simp only [x, if_true, if_false, huv.ne, hvu]
      norm_num
      apply Finset.sum_eq_zero; intro w hw
      simp only [Finset.mem_erase] at hw
      simp [hw.1, hw.2.1]
    -- xᵀLx = 2d+2 (matrix entry computation)
    have hxLx : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x = 2 * (d : ℝ) + 2 := by
      -- xᵀLx = dotProduct x (L *ᵥ x). Reduce inner sum via ite_eq, then outer sum.
      rw [Matrix.toLinearMap₂'_apply']
      simp only [dotProduct, Matrix.mulVec, dotProduct, x]
      -- Reduce inner sum: ∑_j L_{ij} * x_j = L_{iu} - L_{iv}
      simp_rw [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      -- Reduce outer sum: ∑_i (1_u - 1_v) * (L_{iu} - L_{iv})
      --   = (L_{uu} - L_{uv}) - (L_{vu} - L_{vv})
      simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      -- Now goal: L_{uu} - L_{uv} - (L_{vu} - L_{vv}) = 2d+2
      -- L_{uu} = d, L_{uv} = -1 (Adj u v), L_{vu} = -1 (Adj v u), L_{vv} = d
      simp only [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
        Matrix.diagonal_apply, SimpleGraph.adjMatrix, Matrix.of_apply]
      simp [hreg.degree_eq, huv, huv.symm, huv.ne, huv.ne.symm]
      ring
    rw [hxLx, hxx] at hray; linarith
  have hd_pos : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hac_lt_2d : (0 : ℝ) < 2 * (d : ℝ) - algebraicConnectivity G hV := by linarith
  -- Step 7: h ≠ 0 (from ‖h‖² = (2d-ac)·‖f‖² > 0)
  have hh_ne : h ≠ 0 := by
    intro habs
    have hh_zero : ∑ e : G.edgeSet, (h e) ^ 2 = 0 := by simp [show h = 0 from habs]
    rw [hh_norm] at hh_zero
    linarith [mul_pos hac_lt_2d hf_sq_pos]
  -- Step 8: Rayleigh quotient bound
  -- ac(T(G)) ≤ hᵀ L_{T(G)} h / ‖h‖²
  have hRayleigh := algebraicConnectivity_le_rayleigh (triangleGraph G) hTconn hV' h hh_ne hh_sum
  -- Step 9: Bound the Rayleigh quotient
  -- hᵀ L_{T(G)} h / ‖h‖² ≤ ac(G)
  apply le_trans hRayleigh
  -- Goal: hᵀ L_{T(G)} h / ∑ e, (h e)² ≤ ac(G)
  -- Numerator: hᵀ L h = (∑∑ [Adj] (h-h)²) / 2 ≤ (d-1) · ac · ‖f‖²
  have hnum : Matrix.toLinearMap₂' ℝ ((triangleGraph G).lapMatrix ℝ) h h ≤
      ((d : ℝ) - 1) * (algebraicConnectivity G hV * ∑ v, (f v) ^ 2) := by
    -- toLinearMap₂' = indicator_sum / 2
    rw [SimpleGraph.lapMatrix_toLinearMap₂']
    -- Goal: (∑∑ [Adj] (h-h)²) / 2 ≤ (d-1) · ac · ‖f‖²
    have hbound := triangleGraph_quadratic_bound G f d hreg
    -- hbound: ∑∑ [Adj] (h-h)² ≤ 2(d-1) · ∑_e (fu-fv)²
    rw [← hf_edge_energy] at *
    linarith
  -- Denominator: ∑ h² = (2d - ac) · ‖f‖²  (from hh_norm)
  -- Combine: numerator / denominator ≤ (d-1) · ac / (2d - ac) ≤ ac
  -- The last step requires ac ≤ d+1 for d-regular connected graphs.
  rw [hh_norm]
  -- Goal: toLinearMap₂' / ((2d-ac)·‖f‖²) ≤ ac
  -- Need: ac < 2d (for positive denominator) and ac ≤ d+1 (for the bound)
  -- Both are spectral bounds for d-regular connected graphs.
  -- (hac_lt_2d and hac_le_dp1_early already in scope from Step 7)
  have hac_le_dp1 := hac_le_dp1_early
  have hdenom_pos : (0 : ℝ) < (2 * (d : ℝ) - algebraicConnectivity G hV) * ∑ v, (f v) ^ 2 :=
    mul_pos hac_lt_2d hf_sq_pos
  rw [div_le_iff₀ hdenom_pos]
  -- Goal: numerator ≤ ac · (2d-ac) · ‖f‖²
  -- From hnum: numerator ≤ (d-1) · ac · ‖f‖²
  -- Need: (d-1)·ac·‖f‖² ≤ ac·(2d-ac)·‖f‖²
  -- ↔ (d-1) ≤ (2d-ac)  (since ac > 0, ‖f‖² > 0)
  -- ↔ ac ≤ d+1  ✓ (from hac_le_dp1)
  have key : ((d : ℝ) - 1) * (algebraicConnectivity G hV * ∑ v, (f v) ^ 2) ≤
      algebraicConnectivity G hV * ((2 * (d : ℝ) - algebraicConnectivity G hV) * ∑ v, (f v) ^ 2) := by
    have h1 : (d : ℝ) - 1 ≤ 2 * (d : ℝ) - algebraicConnectivity G hV := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg (le_of_lt hac_pos) (le_of_lt hf_sq_pos))]
  linarith

end Topostability
