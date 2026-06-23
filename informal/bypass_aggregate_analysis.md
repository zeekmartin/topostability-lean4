# Can `aggregate_triangle_poincare` be bypassed? — Analysis

**Date:** 2026-06-23
**Repo:** topostability-lean4 · **File:** `Topostability/ConjectureB.lean`
**Context:** after the block-resolvent bridge (commit `cd9d389`,
`Helpers/BlockResolventBridge.lean`, sorry-free).

**Bottom line: NO.** The aggregate Poincaré `triEnergy ≤ 2λ·degQuad` *cannot* be
bypassed by case-restructuring `triEnergy_le_RHS_exists`. Case 1 (`required ≤ 0`,
~97% of graphs) is **logically equivalent to the aggregate** — at the regime
boundary `required = 0` the target `triEnergy ≤ RHS` collapses *exactly* to
`triEnergy ≤ 2λ·degQuad`. There is no slack to exploit.

---

## TASK 1 — `triEnergy_le_RHS_exists` (line 1085)

```lean
theorem triEnergy_le_RHS_exists (lam mE : ℝ)
    (hTconn : (triangleGraph G).Connected)
    (f₀ : V → ℝ) (hf₀norm : ∑ v : V, (f₀ v) ^ 2 = 1) (hf₀perp : ∑ v : V, f₀ v = 0)
    (hf₀eig : (G.lapMatrix ℝ).mulVec f₀ = lam • f₀) :
    ∃ f : V → ℝ, (∑ v : V, (f v) ^ 2 = 1) ∧ (∑ v : V, f v = 0)
      ∧ (G.lapMatrix ℝ).mulVec f = lam • f
      ∧ triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := by
  refine ⟨f₀, hf₀norm, hf₀perp, hf₀eig, ?_⟩
  have haggr : 0 ≤ aggregateSlack G f₀ lam := by
    have := aggregate_triangle_poincare G f₀ lam hf₀eig   -- ← the only use
    simp only [aggregateSlack]; linarith
  have hgap := gapEnergy_nonneg G f₀ lam mE hTconn hf₀eig haggr
  simp only [gapEnergy] at hgap; linarith
```

* **Return type:** existential — `∃ f`, a unit Fiedler (`‖f‖²=1`, `f ⊥ 1`,
  `L f = λf`) with `triEnergy G f ≤ RHS`, where
  `RHS = 2λ(2·degQuad − λ − S²/mE)`. The witness is `f₀` itself.
* **Hypotheses:** `lam mE`, `hTconn` (triangleGraph connected), and a supplied
  unit Fiedler `f₀` with its three eigen/norm/perp facts.
* **How it uses the aggregate:** exactly once, at line 1095, to manufacture
  `haggr : 0 ≤ aggregateSlack = 2λ·degQuad − triEnergy`. This `haggr` is then
  fed to `gapEnergy_nonneg`, which `by_cases` on the sign of `required`.

---

## TASK 2 — the three-case architecture (already present)

`gapEnergy_nonneg` (1055) is the dispatch:

```lean
by_cases hR : required G f lam mE ≤ 0
· exact regime_i_from_aggregate G f lam mE haggr hR              -- Case 1: USES haggr
· exact typeA_extremality_gap_nonneg G f lam mE hTconn heig (not_le.mp hR)  -- Case 2: does NOT use haggr
```

with `gapEnergy = aggregateSlack − required` (`gap_eq_aggregateSlack_sub_required`).

| Case | Condition | Closes via | Uses aggregate? |
|------|-----------|-----------|-----------------|
| **1** | `required ≤ 0` | `regime_i_from_aggregate` (`gap = aggregateSlack − required ≥ 0 − 0`) | **YES — directly** |
| **2A** | `required > 0`, vertex bottleneck | `typeA_slack_ge_required` (1038, SORRY) → now conditionally via `typeA_slack_ge_required_of_resolvent` (BlockResolventBridge) | No |
| **2B** | `required > 0`, path bottleneck | `conjectureB_regime_two_typeB` (810, sorry-free, structural hyps) | No |

**Key structural fact:** the aggregate is consumed in **Case 1 only**. The
regime-ii branch (`typeA_extremality_gap_nonneg`) never touches `haggr`. The
current code merely computes `haggr` *unconditionally up front*, so the
*theorem* depends on the aggregate even on regime-ii inputs — but that is an
artefact of ordering, not a logical need.

### Does `required ≤ 0` *directly* imply `triEnergy ≤ RHS` without the aggregate?

**No — and this is the crux.** `required` is defined purely as

```
required = 2λ(λ + S²/mE − degQuad)
```

It is a function of `λ, S, mE, degQuad` only. It says **nothing** about
`triEnergy`. `required ≤ 0` is just `degQuad ≥ λ + S²/mE`; it is **not** the
statement `T ≤ λ·fᵀDf`. (The task brief's "Required ≤ 0 means T ≤ λ₂·fᵀDf" is
the slip: that bound is the *aggregate*, a separate fact, not a consequence of
`required ≤ 0`.)

---

## TASK 3 — is Case 1 trivial? (working the Lean types)

The proposed chain is correct algebra, but its last link **is** the aggregate.

Identity (pure `ring`, used in `slack_ge_required_of_triEnergy_le_RHS`):

```
RHS  =  2λ(2·degQuad − λ − S²/mE)  =  2λ·degQuad − required.
```

So when `required ≤ 0`:

```
RHS = 2λ·degQuad − required ≥ 2λ·degQuad        (since −required ≥ 0)
```

and therefore

```
triEnergy ≤ RHS   ⟸   triEnergy ≤ 2λ·degQuad.     (★)
```

The hypothesis `triEnergy ≤ 2λ·degQuad` on the right of (★) is **verbatim
`aggregate_triangle_poincare` (line 854)**. So the chain does not *bypass* the
aggregate — it is the most direct *consumer* of it. In `aggregateSlack` terms
this is literally `regime_i_from_aggregate`:

```
gapEnergy = aggregateSlack − required ≥ 0 − 0 = 0
            └ aggregateSlack ≥ 0 is the aggregate ┘  └ required ≤ 0 is the case ┘
```

**Necessity (why no cleverer Case-1 proof exists):** at the regime boundary
`required = 0` the identity gives `RHS = 2λ·degQuad` *exactly*. Hence for any
boundary eigenvector, `triEnergy ≤ RHS` **is** `triEnergy ≤ 2λ·degQuad`. Any
proof of Case 1 that covers the boundary therefore *yields* a proof of the
aggregate for that eigenvector. Case 1 cannot be strictly easier than the
aggregate — they coincide on the boundary.

**Could `aggregate_triangle_poincare_of_maxt` (865) cover Case 1 instead?** Only
partially. It needs `max_e t_e ≤ degQuad` (regular / low-overlap graphs). Its own
docstring (lines 862-864) and line 849 confirm it does **not** cover TYPE A
bottlenecks (`max t_e ≫ degQuad`), and regime-i membership (`required ≤ 0`) does
not imply low triangle overlap. So `of_maxt` closes a *subset* of Case 1, never
all of it.

---

## TASK 4 — refactoring sketch (NOT implemented)

A cleaner architecture *is* possible — push the aggregate inside the `required ≤ 0`
branch so the regime-ii path is provably aggregate-free:

```lean
-- sketch only
refine ⟨f₀, hf₀norm, hf₀perp, hf₀eig, ?_⟩
by_cases hR : required G f₀ lam mE ≤ 0
· -- Case 1: needs triEnergy ≤ 2λ·degQuad  ⇒  STILL the aggregate sorry
  have haggr : 0 ≤ aggregateSlack G f₀ lam := by
    have := aggregate_triangle_poincare G f₀ lam hf₀eig
    simp only [aggregateSlack]; linarith
  have := regime_i_from_aggregate G f₀ lam mE haggr hR
  simp only [gapEnergy] at this; linarith
· -- Case 2 (2A ∪ 2B): required > 0
  have := typeA_extremality_gap_nonneg G f₀ lam mE hTconn hf₀eig (not_le.mp hR)
  simp only [gapEnergy] at this; linarith
  -- 2A still ⇒ typeA_slack_ge_required (1038) sorry, dischargeable conditionally
  --           by typeA_slack_ge_required_of_resolvent (needs partition + hDcore);
  -- 2B closed by conjectureB_regime_two_typeB given structural hyps.
```

**Sorrys remaining after this refactoring:** unchanged.
* `854` `aggregate_triangle_poincare` — still required, now isolated to Case 1.
* `1038` `typeA_slack_ge_required` — unchanged (Case 2A; the bridge is conditional
  on `hDcore` + partition data not in scope here).
* `1121` `conjectureB` — unchanged (graph-level Fiedler-lift reduction).

The only gain is *legibility*: it makes explicit that the aggregate powers Case 1
exclusively and that regime ii is aggregate-independent. It removes **zero**
sorrys.

---

## TASK 5 — Report

**(a) Can `aggregate_triangle_poincare` be bypassed?**  **NO.**
Case 1 (`required ≤ 0`) reduces — necessarily — to `triEnergy ≤ 2λ·degQuad`,
which is the aggregate verbatim. At `required = 0` the target `triEnergy ≤ RHS`
equals `triEnergy ≤ 2λ·degQuad` identically, so Case 1 is no easier than the
aggregate. Restructuring into branches cannot remove it.

**(b) Minimal refactoring (if it helped):** none removes the sorry. The most one
can do is relocate the aggregate call inside the `required ≤ 0` branch (sketch in
TASK 4) for clarity, proving regime ii aggregate-free. Cosmetic, not a bypass.

**(c) New sorry list after any such refactoring:** identical to today —
`{854 aggregate_triangle_poincare, 1038 typeA_slack_ge_required, 1121 conjectureB}`
(3 in `ConjectureB.lean`; `BlockResolventBridge.lean` remains sorry-free).

**(d) Blockers:**
* **Mathematical:** the aggregate is *necessary* for regime i (boundary
  coincidence `RHS = 2λ·degQuad` at `required = 0`). It is the genuine open core
  of Case 1, not an artefact of how the proof is staged.
* **`of_maxt` is not a substitute:** it covers only low-triangle-overlap graphs,
  not all of regime i (TYPE A bottlenecks have `max t_e ≫ degQuad`).
* **No `B2′` route:** `triEnergy ≤ B2′` holds, but `B2′ ≤ 2λ·degQuad` is FALSE on
  sparse-core deg2+dense (line 849, ratio 1.05). The eigenvector equation is
  essential; the aggregate "must be proved directly" (docstring, line 853).

### Where the real leverage is
The aggregate is now the *single* unavoidable analytic sorry for ~97% of graphs
(regime i). Effort is best spent proving `aggregate_triangle_poincare` itself —
and the fixed-quadratic-form routes are already **ruled out** (the `M_C + L`
signed-SOS form is indefinite, `informal/conjecture_B_signed_cancellation.md`;
`φ=M_C f` Rayleigh witnesses overshoot, `informal/conjecture_B_variational_core.md`),
so the proof must use the eigenvector equation `Lu=λu` directly — not on
case-restructuring, which cannot retire it. *(Correction: an earlier draft called
`M_C+L` "the route"; it is a ruled-out route. See `informal/M_C_route_clarification.md`.)*
