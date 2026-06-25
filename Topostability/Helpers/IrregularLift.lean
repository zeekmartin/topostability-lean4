import Topostability.Defs
import Topostability.Shared
import Topostability.Paper13

/-!
# Irregular edge-lift lemmas

Generalizations of the three regular-case lift lemmas from `Paper13`
(`edgeLift_sum_zero`, `edgeLift_norm_fiedler`, `triangleGraph_quadratic_bound`)
to **arbitrary** graphs — i.e. dropping `IsRegularOfDegree d`.

The regular versions exploit `|N(i)| = d` (uniform degree) to collapse degree
sums into `d · (…)`. The general versions keep the per-vertex degree explicit:

* `edgeLift_sum_general` : `∑ₑ (f u + f v) = ∑ᵥ deg(v)·f(v)`.
  (In the regular case `= d·∑f`; the regular `edgeLift_sum_zero` claimed `= 0`
  under `∑f = 0`, which is **false** irregularly — hence the projected lift.)
* `edgeLift_norm_sq_general` / `edgeLift_norm_fiedler_general` :
  `∑ₑ (f u + f v)² = 2·∑ᵥ deg(v)·f(v)² − ∑ₑ (f u − f v)²`.
* `triangleGraph_quadratic_eq_triEnergy` : the **exact** numerator identity
  `∑_{e₁,e₂}[T(G).Adj](h_{e₁}−h_{e₂})² = ∑_{i,j}[i∼j]·|N(i)∩N(j)|·(f_i−f_j)²`
  (the RHS is `triEnergy` unfolded). The regular bound replaced `|N(i)∩N(j)|`
  by its upper bound `d−1`; the irregular route needs the equality.
-/

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **General edge-lift sum.** For any graph, the sum of the edge lift equals the
degree-weighted vertex sum: `∑ₑ (f u + f v) = ∑ᵥ deg(v)·f(v)`. Each vertex `v`
appears in exactly `deg(v)` edges. Generalizes `edgeLift_sum_regular` by replacing
`|N(i)| = d` with `|N(i)| = deg(i)`; the dart double-counting is degree-agnostic. -/
lemma edgeLift_sum_general (f : V → ℝ) :
    ∑ e : G.edgeSet, edgeLift G f e = ∑ v : V, (G.degree v : ℝ) * f v := by
  classical
  -- Step 1: double sum = 2 · ∑ deg·f
  have hdouble : ∑ i : V, ∑ j : V,
      (if G.Adj i j then f i + f j else (0 : ℝ)) = 2 * ∑ v, (G.degree v : ℝ) * f v := by
    simp_rw [show ∀ (i j : V), (if G.Adj i j then f i + f j else (0 : ℝ)) =
      (if G.Adj i j then f i else 0) + (if G.Adj i j then f j else 0) from
      fun i j => by split_ifs <;> simp]
    simp_rw [Finset.sum_add_distrib]
    -- Part A: ∑_i ∑_j [Adj i j] fi = ∑_i deg(i)·fi
    have hA : ∑ i : V, ∑ j : V, (if G.Adj i j then f i else (0 : ℝ)) =
        ∑ v, (G.degree v : ℝ) * f v := by
      simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show ((Finset.univ.filter (G.Adj i)).card : ℝ) = (G.degree i : ℝ) from by
        rw [show Finset.univ.filter (G.Adj i) = G.neighborFinset i from
          (SimpleGraph.neighborFinset_eq_filter G).symm]; rfl]
    -- Part B: ∑_i ∑_j [Adj i j] fj = ∑_j deg(j)·fj (swap sums, adj_comm gives hA)
    have hB : ∑ i : V, ∑ j : V, (if G.Adj i j then f j else (0 : ℝ)) =
        ∑ v, (G.degree v : ℝ) * f v := by
      have hswap : ∀ (a b : V), (if G.Adj b a then f a else (0 : ℝ)) =
          (if G.Adj a b then f a else 0) := by
        intro a b; congr 1; exact propext (G.adj_comm b a)
      rw [Finset.sum_comm]; simp_rw [hswap]; exact hA
    rw [hA, hB]; ring
  -- Step 2: edge sum = double sum / 2 (via dart decomposition) — degree-agnostic,
  -- copied verbatim from `edgeLift_sum_regular`.
  suffices hedge : (∑ e : G.edgeSet, edgeLift G f e) * 2 =
      ∑ i : V, ∑ j : V, if G.Adj i j then f i + f j else (0 : ℝ) by
    linarith
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
    simp only [SimpleGraph.dartOfNeighborSet, Finset.sum_filter]
    conv_rhs => rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (Finset.univ.filter (G.Adj v))
      (fun w => by simp [SimpleGraph.mem_neighborSet])
      (fun w => f v + f w)).symm
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
  have h3 : ∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => f u + f v, fun u v => add_comm _ _⟩ e =
      ∑ e : G.edgeSet, edgeLift G f e := by
    simp only [edgeLift]
    rw [← Finset.sum_coe_sort]
    exact @Fintype.sum_equiv _ _ ℝ _ _ _
      (Equiv.subtypeEquivRight (fun _ => SimpleGraph.mem_edgeFinset (G := G)))
      _ _ (fun _ => rfl)
  linarith [h1, h2, h3]

/-- **General edge-lift norm² (expanded).** `∑ₑ (f u + f v)² = ∑ᵥ deg(v)·f(v)²
+ 2·∑ₑ f u · f v`. Generalizes `edgeLift_norm_sq`. -/
lemma edgeLift_norm_sq_general (f : V → ℝ) :
    ∑ e : G.edgeSet, (edgeLift G f e) ^ 2 =
    (∑ v, (G.degree v : ℝ) * (f v) ^ 2) + 2 * ∑ e : G.edgeSet,
      Sym2.lift ⟨fun u v => f u * f v, fun u v => by ring⟩ e.val := by
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
  exact edgeLift_sum_general G (fun v => (f v) ^ 2)

/-- **General edge-lift norm² (Fiedler form).** `∑ₑ (f u + f v)² = 2·∑ᵥ deg(v)·f(v)²
− ∑ₑ (f u − f v)²`. Generalizes `edgeLift_norm_fiedler`: the regular RHS
`(2d − λ)·‖f‖²` becomes `2·(∑ deg·f²) − (∑ₑ (f u − f v)²)`, where the last sum is
`fᵀL_G f` (`= λ·‖f‖²` for a `λ`-eigenvector). No spectral hypothesis assumed. -/
lemma edgeLift_norm_fiedler_general (f : V → ℝ) :
    ∑ e : G.edgeSet, (edgeLift G f e) ^ 2 =
    2 * (∑ v, (G.degree v : ℝ) * (f v) ^ 2)
      - ∑ e : G.edgeSet, Sym2.lift ⟨fun u v => (f u - f v) ^ 2, fun u v => by ring⟩ e.val := by
  rw [edgeLift_norm_sq_general G f]
  -- ∑_e (fu²+fv²) = ∑ deg·f²
  have hsq_sum : ∑ e : G.edgeSet,
      Sym2.lift ⟨fun u v => (f u) ^ 2 + (f v) ^ 2, fun u v => by ring⟩ e.val =
      ∑ v, (G.degree v : ℝ) * (f v) ^ 2 := by
    have := edgeLift_sum_general G (fun v => (f v) ^ 2)
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
      (∑ v, (G.degree v : ℝ) * (f v) ^ 2) -
      2 * ∑ e : G.edgeSet,
        Sym2.lift ⟨fun u v => f u * f v, fun u v => by ring⟩ e.val := by
    simp_rw [hexpand, Finset.sum_sub_distrib, ← Finset.mul_sum, hsq_sum]
  linarith [henergy]

section QuadEq
attribute [local instance] Classical.propDecidable

/-- **Exact numerator identity (irregular).** The `T(G)`-Laplacian quadratic form of
the edge lift equals `triEnergy` (the RHS is `triEnergy G f` unfolded): the inner
`∑_u` over common neighbours of an edge `{v,w}` collapses to `|N(v)∩N(w)|`.
This is the equality the regular `triangleGraph_quadratic_bound` relaxed to `≤ 2(d−1)·…`. -/
lemma triangleGraph_quadratic_eq_triEnergy (f : V → ℝ) :
    (∑ e₁ : G.edgeSet, ∑ e₂ : G.edgeSet,
      if (triangleGraph G).Adj e₁ e₂
      then (edgeLift G f e₁ - edgeLift G f e₂) ^ 2
      else (0 : ℝ)) =
    ∑ i : V, ∑ j : V,
      if G.Adj i j
      then ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) * (f i - f j) ^ 2
      else (0 : ℝ) := by
  rw [triangleGraph_quadratic_form]
  -- ∑_u∑_v∑_w [Adj uv ∧ Adj uw ∧ Adj vw] (fv-fw)²  →  ∑_v∑_w∑_u
  rw [Finset.sum_comm (f := fun u v => _)]
  conv_lhs => arg 2; ext v; rw [Finset.sum_comm (f := fun u w => _)]
  -- factor (fv-fw)² out of the u-sum: ∑_u [P u] = |filter P|
  conv_lhs => arg 2; ext v; arg 2; ext w
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
  by_cases hvw : G.Adj v w
  · rw [if_pos hvw]
    have hset : Finset.univ.filter (fun u => G.Adj u v ∧ G.Adj u w ∧ G.Adj v w)
        = G.neighborFinset v ∩ G.neighborFinset w := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h1.symm, h2.symm⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm, hvw⟩
    rw [hset]
  · rw [if_neg hvw]
    have hcard : (Finset.univ.filter (fun u => G.Adj u v ∧ G.Adj u w ∧ G.Adj v w)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun u _ h => hvw h.2.2
    rw [hcard]; simp

end QuadEq

end Topostability
