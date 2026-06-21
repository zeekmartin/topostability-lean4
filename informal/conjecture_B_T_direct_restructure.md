# Conjecture B — restructure to the direct `T ≤ λ₂G` (extremizer = `K_n`)

Per the strategic finding (`conjecture_B_true_T_vs_B2prime.md`): the `B2′` relaxation was the wrong
target (its hard case is the deg2+dense bottleneck, a `B2′` artifact), whereas the *direct*
`T ≤ λ₂G` has its extremizer at the complete graph `K_n` (benign). This round restructures the Lean
sorry accordingly, and **honestly tests** the "regular case proved + irregularity slack" route — which
**does not work** as stated.

## TASK 1 + 4 — Lean restructure (build 2688 OK)

- **New sorry `triEnergy_le_RHS`** : `triEnergy G f ≤ 2λ(2fᵀDf − λ − S²/m)` — the direct `T ≤ λ₂G`,
  no `B2′` intermediary.
- **`conjectureB_lift = triEnergy_le_RHS`** (one step), and **`conjectureB_regime_two = triEnergy_le_RHS`**
  (the `hReq` hypothesis is now unused — the bound holds for all graphs).
- **Removed** `B2prime_le_RHS`. **Kept** `triEnergy_le_B2prime` (sorry-free, `T ≤ B2′`) as an
  *independent* off-chain result, and `aggregate_triangle_poincare` (open, off-chain).
- `conjectureB_regime_two_typeB` unchanged (TYPE B, sorry-free given block hypotheses).

**Sorry ledger (3, unchanged count):** `aggregate_triangle_poincare` (648, off-chain),
**`triEnergy_le_RHS` (772, the lift content — direct `T ≤ λ₂G`)**, `conjectureB` (811, lift reduction).
`conjectureB_lift` now depends on the single sorry `triEnergy_le_RHS`.

## TASK 2 — the premise "aggregate_regular proves the regular case" is FALSE

`aggregate_triangle_poincare_regular` gives `T ≤ 2λ·fᵀDf`. For the conclusion `T ≤ RHS = 2λ(2fᵀDf − λ
− S²/m)` this needs `2fᵀDf ≥ 2fᵀDf − λ − S²/m`-type slack, i.e. `Required = λ(λ + S²/m − fᵀDf) ≤ 0`.
**But `K_n` has `Required > 0`** (e.g. `K₁₀`: `Required = +10`), so the regime-(i) logic does *not*
apply, and the aggregate bound **overshoots**:

| graph | `T_ord` | `RHS` | `2λ·fᵀDf` (aggregate) | aggregate `≤ RHS`? |
|---|---|---|---|---|
| K₁₀ | 160 | 160 | 180 | **NO** |
| K₃₀ | 1680 | 1680 | 1740 | **NO** |
| rr(20,6) (sparse) | 4.7 | 47.3 | 29.8 | yes (Required<0) |

> **`aggregate_triangle_poincare_regular` does NOT prove the regular case of `triEnergy_le_RHS`.** On
> `K_n` (the extremizer, Required > 0) it gives a strictly *looser* bound. `triEnergy_le_RHS` is *tight*
> (equality) at `K_n` and is genuinely open even for regular graphs.

The regular case *does* reduce, via `T ≤ B2′` (`triEnergy_le_B2prime`, sorry-free), to
`B2′ = (d−1)·2λ ≤ RHS ⟺ λ₂ + S²/m ≤ d+1` — a clean spectral inequality, equality at `K_n` (`λ₂ = d+1`,
`S = 0`). So the regular case is `λ₂ + S²/m ≤ d+1`, not anything `aggregate_regular` supplies.

## TASK 3 — the "irregularity slack" route FAILS

`slack := 1 − T/(λ₂G)`. Correlation with irregularity measures (broad corpus):

| measure | `corr(slack, ·)` |
|---|---|
| normalized degree variance `Var(d)/d̄²` | +0.38 |
| `S²/m` | +0.20 |
| `Δ/δ` | +0.18 |
| raw degree variance | +0.15 |

> **Irregularity does NOT predict the slack** (best correlation `0.38`). Decisively, **regular graphs
> themselves span `slack ∈ [0, 0.998]`**: `K_n` has `slack = 0`, dense regular `rr(n,n−3)` has
> `0.07–0.22`, but sparse regular `rr(n,4)` has **`slack = 0.95–0.998`**. So `slack = 0` is *not* the
> regular case — it is *only* `K_n` (and graphs near-complete). The slack vanishes with **density**
> (closeness to `K_n`), not with regularity.

Hence the proposed "regular base (slack 0) + irregularity-slack bound `slack ≥ c·irregularity`" **does
not hold**: the slack-0 set is `{K_n}`, not the regular graphs, and `slack ≥ c·(degree variance)`
fails (regular graphs have variance 0 but slack up to 0.998).

## Honest conclusion

- **The restructure (TASK 1/4) is done and correct:** the Lean sorry is now the direct `T ≤ λ₂G`
  (`triEnergy_le_RHS`), whose extremizer is the complete graph `K_n` — a better-conditioned target than
  the `B2′`-relaxed sorry (whose hard case was the deg2+dense artifact). Build 2688 OK, 3 sorrys,
  `conjectureB_lift` depends on the single `triEnergy_le_RHS`.
- **But the "regular + slack" proof route (TASK 2/3) does NOT work:**
  - `aggregate_triangle_poincare_regular` does *not* prove the regular case (`K_n` is Required > 0, the
    aggregate bound overshoots `RHS`);
  - the slack is *not* driven by irregularity (corr `0.38`; regular graphs span slack `0–0.998`); it
    vanishes only at `K_n` (by **density**, not regularity).
- **The genuine structure of `T ≤ λ₂G`:** tight (equality) at the complete graph `K_n`; the slack grows
  as the graph thins from complete (and is large on *both* sparse-regular and bottleneck graphs). The
  regular case itself reduces to `λ₂ + S²/m ≤ d+1` (clean spectral, equality at `K_n`); the general case
  needs a density/completeness-monotone argument, **not** an irregularity-slack one.

So the right next target is `triEnergy_le_RHS` with the **complete graph as the unique equality case**,
proved by a *completeness*-monotonicity (slack increases as edges are removed from `K_n`) — the
edge-deletion increment `δ` machinery (`conjecture_B_typeA_delta_rigor.md`,
`eigenpair_invariance_equal_values`) is the relevant tool, now applied to `T` directly rather than
`B2′`.

## Lean
`triEnergy_le_RHS` (new sorry, direct `T ≤ λ₂G`); `conjectureB_lift`, `conjectureB_regime_two` now
its one-step applications (sorry-free declarations). `triEnergy_le_B2prime` (sorry-free) and
`aggregate_triangle_poincare` (open) retained off-chain. `CONJECTURE_B_STATUS.md` §3/§6 updated.
