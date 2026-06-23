import Topostability.ConjectureB

/-!
# Block-resolvent scalar bridge for Conjecture B — Case 2A (regime ii, TYPE A)

This file formalises — **sorry-free** and **conditionally** — the scalar bridge that closes the
regime-ii TYPE A branch of Conjecture B, isolating the single *non-numerical* hypothesis (the
**block resolvent bound**) that holds numerically on every tested graph (17/17, max ratio 0.952)
but cannot yet be derived inside Lean: it needs matrix-inverse / Cauchy-interlacing infrastructure
that is currently absent from Mathlib.

## The reduction chain

`typeA_slack_ge_required` (in `ConjectureB.lean`) asks for `required ≤ aggregateSlack`. The
sorry-free partition bound `triEnergy_le_of_partition` shows this is implied by `triEnergy ≤ RHS`
with `RHS = 2λ(2·fᵀDf − λ − S²/mE)`, which in turn follows from the scalar **flatness** condition

  `(δ−1)·D_port + maxt_core·D_core ≤ RHS`.

The **block resolvent bound** discharges the `D_core` term:

  `D_core = dirichletOn(core) ≤ ρ · sourceNormSq`,

where — crucially — `sourceNormSq` is the *corrected* source norm

  `s_v = Σ_{u~v, u∈P} f_u − d_v^P · f_v`,  `sourceNormSq = Σ_v s_v²`,

which is **NOT** equal to `D_port` in general (the identity `‖s‖² = D_port` fails, e.g. on the twin
family, 8/17). After substituting the resolvent bound, what remains is a pure scalar flatness
inequality `(δ−1)·D_port + maxt_core·ρ·sourceNormSq ≤ RHS`.

`typeA_slack_ge_required_of_resolvent` below packages exactly this: it is sorry-free and takes the
block resolvent bound `hDcore` and the residual flatness `hflat` as explicit hypotheses, proving the
TYPE A target `required ≤ aggregateSlack`. The block resolvent bound `hDcore` is the EXACT remaining
semantic gap; everything else is mechanical (per-class triangle-count bounds + `linarith`/`ring`).
-/

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Algebraic bridge (no `sorry`).** `triEnergy ≤ RHS` is *equivalent* to the TYPE A target
`required ≤ aggregateSlack`, because `RHS = 2λ·degQuad − required`, i.e.
`aggregateSlack − (RHS − triEnergy) = required` (pure algebra over a field). -/
lemma slack_ge_required_of_triEnergy_le_RHS (f : V → ℝ) (lam mE : ℝ)
    (h : triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE)) :
    required G f lam mE ≤ aggregateSlack G f lam := by
  have e : required G f lam mE
      = aggregateSlack G f lam
        - (2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) - triEnergy G f) := by
    simp only [required, aggregateSlack]; ring
  rw [e]; linarith

/-- **Block-resolvent scalar bridge (no `sorry`).** The conditional reduction of the regime-ii TYPE A
target `required ≤ aggregateSlack` to the single **block resolvent bound** `hDcore`.

Inputs:
* `hport`, `hcore` — the mechanical per-class triangle-count bounds (`t_e ≤ Cp = δ−1` on port edges,
  `t_e ≤ Cc = maxt_core` on core edges);
* `hCc` — `0 ≤ maxt_core` (a triangle count is nonnegative);
* `hDcore` — the **block resolvent bound** `D_core = dirichletOn(core) ≤ ρ · sourceNormSq` (the EXACT
  remaining semantic gap; `sourceNormSq` is the corrected source norm, *not* `D_port`);
* `hflat` — the residual scalar flatness inequality
  `Cp·D_port + Cc·(ρ·sourceNormSq) ≤ RHS`.

Everything but `hDcore` is mechanical; this isolates the resolvent bound as the only inequality that
still relies on Mathlib infrastructure not yet available. -/
theorem typeA_slack_ge_required_of_resolvent
    (f : V → ℝ) (lam mE : ℝ) (P : V → V → Prop) (Cp Cc rho sourceNormSq : ℝ)
    (hport : ∀ i j, G.Adj i j → P i j →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ Cp)
    (hcore : ∀ i j, G.Adj i j → ¬ P i j →
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) ≤ Cc)
    (hCc : 0 ≤ Cc)
    (hDcore : dirichletOn G (fun i j => ¬ P i j) f ≤ rho * sourceNormSq)
    (hflat : Cp * dirichletOn G P f + Cc * (rho * sourceNormSq)
        ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE)) :
    required G f lam mE ≤ aggregateSlack G f lam := by
  -- Discharge the `D_core` term via the resolvent bound (monotone in `Cc ≥ 0`).
  have hcond : Cp * dirichletOn G P f + Cc * dirichletOn G (fun i j => ¬ P i j) f
      ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := by
    have hmono : Cc * dirichletOn G (fun i j => ¬ P i j) f ≤ Cc * (rho * sourceNormSq) :=
      mul_le_mul_of_nonneg_left hDcore hCc
    linarith
  -- Partition bound ⇒ `triEnergy ≤ RHS` ⇒ `required ≤ aggregateSlack`.
  exact slack_ge_required_of_triEnergy_le_RHS G f lam mE
    (triEnergy_le_of_partition G P f Cp Cc _ hport hcore hcond)

end Topostability
