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

/-- **Aggregate triangle-Poincaré (OPEN).** `T ≤ λ₂·fᵀDf` (ordered: `T_ord ≤ 2λ₂·fᵀDf`).

This is `Σ_c E_{G[N(c)]}(f) ≤ λ₂·Σ_c (Σ_{v∈N(c)} f_v²)` summed via the apex identity
(`apex_triangle_energy_identity`, `Paper15`). The *local* Poincaré
`E_{G[N(c)]}(f) ≤ λ₂·Σ_{N(c)}f²` fails on ~6% of apices, but the aggregate holds on every
tested graph (0 violations). Proof path open. -/
lemma aggregate_triangle_poincare (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    triEnergy G f ≤ 2 * lam * degQuad G f := by
  sorry

/-- **Regime (ii): `Required > 0` (OPEN).** The bottleneck regime. Empirically the slack
`Deficit − Required = RHS − T` stays positive with `Deficit/Required ≥ 1.7`; no closed-form
proof yet (every edge/apex-local bound is either invalid on the bottleneck edges or too
loose on the dense edges — see the `informal/` analyses). -/
lemma conjectureB_regime_two (f : V → ℝ) (lam mE : ℝ) (hmE : 0 < mE) (hlam : 0 < lam)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hReq : degQuad G f < lam + (degLin G f) ^ 2 / mE) :
    triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := by
  sorry

/-- **Conjecture B — triangle-energy lift inequality.** For a unit Fiedler vector `f`
(`L_G f = λ₂ f`, `λ₂ > 0`) and `mE = |E| > 0`:
`T ≤ λ₂·(fᵀQf − S²/m)`, ordered form `T_ord ≤ 2λ₂(2fᵀDf − λ₂ − S²/mE)`.

This implies `λ₂(T(G)) ≤ λ₂(G)` (Conjecture B) via the projected Fiedler lift. Proof: a
regime split on `sign(Required)`; **regime (i) is closed** here (modulo the aggregate
Poincaré), regime (ii) is the open lemma. -/
theorem conjectureB_lift (f : V → ℝ) (lam mE : ℝ) (hmE : 0 < mE) (hlam : 0 < lam)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := by
  by_cases hReq : lam + (degLin G f) ^ 2 / mE - degQuad G f ≤ 0
  · -- Regime (i): Required ≤ 0  ⇒  fᵀDf ≥ λ₂ + S²/m  ⇒  fᵀQf − S²/m ≥ fᵀDf.
    have hpoin := aggregate_triangle_poincare G f lam heig
    calc triEnergy G f
        ≤ 2 * lam * degQuad G f := hpoin
      _ ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  · -- Regime (ii): Required > 0.
    push_neg at hReq
    exact conjectureB_regime_two G f lam mE hmE hlam heig (by linarith)

/-- **Conjecture B (graph statement).** For connected `G` with `T(G)` connected,
`λ₂(T(G)) ≤ λ₂(G)`. Reduces to `conjectureB_lift` via the projected Fiedler lift
`h' = Bᵀf − (S/m)1_E ⊥ 1_E` together with `t_ab ≤ min(d_a,d_b)−1`
(`triCount_le_min_degree_sub_one`); that lift reduction is not yet formalised. -/
theorem conjectureB (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (hTV : Fintype.card (G.edgeSet) ≥ 2) (hTconn : (triangleGraph G).Connected) :
    algebraicConnectivity (triangleGraph G) hTV ≤ algebraicConnectivity G hV := by
  sorry

end Topostability
