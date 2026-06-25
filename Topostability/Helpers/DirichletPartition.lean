import Topostability.Helpers.BlockResolventBridge

/-!
# Case 2A Dirichlet-partition bridge for Conjecture B (regime ii, TYPE A)

A **sorry-free, resolvent-free** reduction of the regime-ii TYPE A target
`required ≤ aggregateSlack` to a single *elementary* scalar inequality.

It replaces the unformalizable block-resolvent bound `D_core ≤ ρ·sourceNormSq`
(`Helpers/BlockResolventBridge.lean`, needs matrix-inverse / Cauchy-interlacing
infrastructure absent from Mathlib) by the **exact Dirichlet partition identity**

  `D_core + D_cross + D_pp = (total edge Dirichlet)`            (`dirichlet_partition_eq`)

verified numerically on the 17 Case 2A graphs (`informal/dcore_simple_bound.md`,
`task0_dirichlet_bridge_verify.py`: partition exact to 2.8e-14, `t_pp = 0`,
scalar closes at ratio 0.935).

The port split (low-degree vertices `isPort`) cuts every edge into three classes by
how many endpoints are ports — `cross` (one), `core` (none), `pp` (two). On the 17
graphs the port-port edges carry **no triangles** (`t_pp = 0`), so they contribute `0`
to `triEnergy`; the three-class bound is therefore strictly tighter than any two-class
split and is exactly what closes `hcond`. -/

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Tight three-class triangle-energy bound (no `sorry`).** Splitting edges by the port
predicate `isPort` into `cross`/`core`/`pp`, and using that port-port edges carry no
triangles (`hpp : t = 0`), the triangle energy is bounded by the *cross* and *core*
Dirichlet energies only — the port-port edges drop out (coefficient `0`). This is the
inequality the two-class `triEnergy_le_of_partition` cannot give (it would over-charge the
high-energy zero-triangle port-port edges at rate `Cc`). -/
lemma triEnergy_le_cross_core (f : V → ℝ) (isPort : V → Prop) (Cp Cc : ℝ)
    (hcross : ∀ i j, G.Adj i j → ((isPort i ∧ ¬ isPort j) ∨ (¬ isPort i ∧ isPort j)) →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ Cp)
    (hcore : ∀ i j, G.Adj i j → (¬ isPort i ∧ ¬ isPort j) →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ Cc)
    (hpp : ∀ i j, G.Adj i j → (isPort i ∧ isPort j) →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) = 0) :
    triEnergy G f ≤
      Cp * dirichletOn G (fun i j => (isPort i ∧ ¬ isPort j) ∨ (¬ isPort i ∧ isPort j)) f
      + Cc * dirichletOn G (fun i j => ¬ isPort i ∧ ¬ isPort j) f := by
  classical
  unfold triEnergy dirichletOn
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hadj : G.Adj i j
  · rw [if_pos hadj]
    by_cases hpi : isPort i <;> by_cases hpj : isPort j
    · -- port-port: cross & core both false; triangle count = 0
      rw [if_neg (by tauto), if_neg (by tauto), hpp i j hadj ⟨hpi, hpj⟩]
      simp
    · -- cross (i port, j not)
      rw [if_pos ⟨hadj, Or.inl ⟨hpi, hpj⟩⟩, if_neg (by tauto), mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (hcross i j hadj (Or.inl ⟨hpi, hpj⟩)) (sq_nonneg _)
    · -- cross (j port, i not)
      rw [if_pos ⟨hadj, Or.inr ⟨hpi, hpj⟩⟩, if_neg (by tauto), mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (hcross i j hadj (Or.inr ⟨hpi, hpj⟩)) (sq_nonneg _)
    · -- core (neither port)
      rw [if_neg (by tauto), if_pos ⟨hadj, hpi, hpj⟩, mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_right (hcore i j hadj ⟨hpi, hpj⟩) (sq_nonneg _)
  · simp [hadj]

/-- **Dirichlet partition identity (no `sorry`).** The three port classes
`cross`/`core`/`pp` partition every ordered pair, so their Dirichlet energies sum to the
full edge Dirichlet energy `∑_{i,j} [i∼j] (f_i − f_j)²`. (For a unit `λ₂`-eigenvector the
RHS equals `2·λ₂` via `quadratic_form_eq_edge_sum`; that spectral step is supplied where the
identity is used, keeping this lemma purely combinatorial.) -/
lemma dirichlet_partition_eq (f : V → ℝ) (isPort : V → Prop) :
    dirichletOn G (fun i j => (isPort i ∧ ¬ isPort j) ∨ (¬ isPort i ∧ isPort j)) f
    + dirichletOn G (fun i j => ¬ isPort i ∧ ¬ isPort j) f
    + dirichletOn G (fun i j => isPort i ∧ isPort j) f
    = ∑ i : V, ∑ j : V, if G.Adj i j then (f i - f j) ^ 2 else 0 := by
  classical
  unfold dirichletOn
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hadj : G.Adj i j
  · by_cases hpi : isPort i <;> by_cases hpj : isPort j <;> simp [hadj, hpi, hpj]
  · simp [hadj]

/-- **Case 2A Dirichlet bridge (no `sorry`).** The conditional, resolvent-free reduction of
the regime-ii TYPE A target `required ≤ aggregateSlack` to the elementary scalar inequality
`hscalar`.

Inputs:
* `hcross`, `hcore`, `hpp` — the mechanical per-class triangle-count bounds: cross edges have
  `t ≤ Cp` (`= δ−1`), core edges `t ≤ Cc` (`= maxt_core`), and **port-port edges have
  `t = 0`** (the verified Case 2A structural fact);
* `hpartition` — the **Dirichlet partition identity** `D_core + D_cross + D_pp = Dtot`
  (`= dirichlet_partition_eq` paired with `total edge Dirichlet = Dtot`; for a unit Fiedler
  `Dtot = 2·λ₂`). This is the elementary replacement for the resolvent bound;
* `hscalar` — the residual scalar flatness inequality, stated via the identity with `D_core`
  eliminated (`D_core = Dtot − D_cross − D_pp`):
  `Cp·D_cross + Cc·(Dtot − D_cross − D_pp) ≤ RHS`.

Everything but `hscalar` is now provable in current Mathlib — the matrix-inverse hypothesis of
`typeA_slack_ge_required_of_resolvent` is gone, replaced by the exact `hpartition`. -/
theorem typeA_slack_ge_required_of_dirichlet
    (f : V → ℝ) (lam mE : ℝ) (isPort : V → Prop) (Cp Cc Dtot : ℝ)
    (hcross : ∀ i j, G.Adj i j → ((isPort i ∧ ¬ isPort j) ∨ (¬ isPort i ∧ isPort j)) →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ Cp)
    (hcore : ∀ i j, G.Adj i j → (¬ isPort i ∧ ¬ isPort j) →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ Cc)
    (hpp : ∀ i j, G.Adj i j → (isPort i ∧ isPort j) →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) = 0)
    (hpartition :
        dirichletOn G (fun i j => ¬ isPort i ∧ ¬ isPort j) f
        + dirichletOn G (fun i j => (isPort i ∧ ¬ isPort j) ∨ (¬ isPort i ∧ isPort j)) f
        + dirichletOn G (fun i j => isPort i ∧ isPort j) f = Dtot)
    (hscalar :
        Cp * dirichletOn G (fun i j => (isPort i ∧ ¬ isPort j) ∨ (¬ isPort i ∧ isPort j)) f
        + Cc * (Dtot
            - dirichletOn G (fun i j => (isPort i ∧ ¬ isPort j) ∨ (¬ isPort i ∧ isPort j)) f
            - dirichletOn G (fun i j => isPort i ∧ isPort j) f)
        ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE)) :
    required G f lam mE ≤ aggregateSlack G f lam := by
  -- (1) tight three-class triangle-energy bound
  have htri := triEnergy_le_cross_core G f isPort Cp Cc hcross hcore hpp
  -- (2) eliminate `D_core` via the partition identity: D_core = Dtot − D_cross − D_pp
  have hcore_eq :
      dirichletOn G (fun i j => ¬ isPort i ∧ ¬ isPort j) f
      = Dtot
        - dirichletOn G (fun i j => (isPort i ∧ ¬ isPort j) ∨ (¬ isPort i ∧ isPort j)) f
        - dirichletOn G (fun i j => isPort i ∧ isPort j) f := by
    linarith [hpartition]
  rw [hcore_eq] at htri
  -- (3) triEnergy ≤ RHS, then the existing sorry-free algebraic bridge
  exact slack_ge_required_of_triEnergy_le_RHS G f lam mE (le_trans htri hscalar)

end Topostability
