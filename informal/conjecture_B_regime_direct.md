# Conjecture B — direct `T ≤ RHS` per regime (does it bypass aggregate Poincaré?)

`RHS = λ₂(fᵀQf − S²/m) = λ₂(2fᵀDf − λ₂ − S²/m)`, `B(lift) ⟺ T ≤ RHS`.
`Required = λ₂(λ₂ + S²/m − fᵀDf)`; regime (i) `Required ≤ 0 ⟺ fᵀAf = fᵀDf − λ₂ ≥ S²/m`.
Goal: prove each regime directly, *without* the aggregate Poincaré `T ≤ λ₂fᵀDf` as intermediary.
Code: [`conjecture_B_regime_direct.py`](../conjecture_B_regime_direct.py), 580 graphs (regime (i):
277, regime (ii): 303), all residuals machine-zero.

**Verdict: the proposed bypass (TASK 3) is FALSE.** Discarding `Open` does not close regime (i);
`Open` is load-bearing, and aggregate Poincaré (or the genuine `T ≤ RHS`) is still required.

---

## Three exact slack identities

| identity | residual |
|---|---|
| `A2_diag − RHS = λ₂S²/m − Cov_L(d,f²)`,  `A2_diag := Σ_v[σ_v−(d_v−λ₂)²]f_v² = T + Open` | `8·10⁻¹²` |
| `RHS − T = Open + Cov_L(d,f²) − λ₂S²/m` (lift slack) | `8·10⁻¹²` |
| `RHS − T = (−Q) − Required` (`−Q = λ₂fᵀDf − T` = aggregate-Poincaré slack) | `2·10⁻¹³` |

These come from `A2_diag = 2λ₂fᵀDf − λ₂² − 𝒜` and `RHS = 2λ₂fᵀDf − λ₂² − λ₂S²/m` (`𝒜 = Cov_L(d,f²)`).
The last one says the **lift slack equals the aggregate-Poincaré slack minus `Required`** — so in
regime (i) (`Required ≤ 0`) the lift bound is *easier* than aggregate Poincaré by exactly `|Required|`.

## TASK 1 — margins in regime (i): direct vs aggregate Poincaré

| margin | min | median |
|---|---|---|
| `margin_direct = (RHS − T)/RHS` | `0.295` | `0.813` |
| `margin_AP = (λ₂fᵀDf − T)/(λ₂fᵀDf)` | `0.233` | `0.744` |

The direct bound `T ≤ RHS` has **strictly more margin** than aggregate Poincaré in regime (i)
(consistent with `RHS ≥ λ₂fᵀDf` there). The tightest regime-(i) graph has `T/RHS = 0` (a corpus
graph with essentially no triangles on the Fiedler-active edges). So regime (i) direct B is
*comfortable* — the obstruction is the proof *route*, not tightness.

## TASK 2/3 — `A2_diag ≤ RHS`? (the proposed bypass) — **FALSE**

The bypass hoped `T ≤ T + Open = A2_diag ≤ RHS`, discarding `Open ≥ 0`. But

> `A2_diag − RHS = λ₂S²/m − Cov_L(d,f²)`, and `Cov_L(d,f²)` is **negative on most graphs**,

so `A2_diag > RHS` almost always:

| test | holds |
|---|---|
| `A2_diag ≤ RHS` (all graphs) | `22/580` |
| `A2_diag ≤ RHS` (regime (i) only) | **`20/277`** |
| (`⟺ Cov_L(d,f²) ≥ λ₂S²/m`) | same |

In regime (i), `A2_diag − RHS` has median `+4.5` (max `315`) — `A2_diag` overshoots `RHS` massively.
The discarded `Open` is **larger than the lift slack** (`Open/(RHS−T)` median `1.54`): you cannot
throw `Open` away. **`Open` is load-bearing**, as every prior round found. The bypass is dead.

## TASK 4/5 — regime (ii): `T ≤ RHS` holds with margin

Regime (ii) (`Required > 0`, 303 graphs, almost all the `corpus` family — the bottleneck families
`barbell/chain` mostly sit in regime (i)):

| | `T/RHS` |
|---|---|
| min | `0.011` |
| median | `0.335` |
| **max** | **`0.829`** |

`B` holds on all 303 (`T/RHS ≤ 0.83`, ≥17% margin). A clean TYPE A (vertex) / TYPE B (path)
split as in [`conjecture_B_final_classification.md`](conjecture_B_final_classification.md) would need
the boundary-ratio machinery (not recomputed here); but the data confirms regime (ii) `B` is not
tight. TYPE B (path/lollipop) graphs have `T = O(λ₂²)`, `RHS = Θ(λ₂)`, so `T/RHS → 0` (the small
`T/RHS = 0.011` tail); TYPE A (vertex/deg2+dense) have small `T` (few triangles on bottleneck edges)
against `RHS = λ₂·Var(h) > 0`.

## TASK 6 — coverage: the bypass does NOT eliminate aggregate Poincaré

`B = T ≤ RHS` holds `580/580`. But:

- **regime (i) is NOT closed by `A2_diag ≤ RHS`** (only `20/277`). It is closed in the formalization
  only via aggregate Poincaré: `T ≤ λ₂fᵀDf ≤ RHS` (the `≤ RHS` step is free since `RHS ≥ λ₂fᵀDf`).
- regime (ii) `B` holds `303/303` with margin (TASK 4/5).

So the three-way decomposition **fails at regime (i)**: the open lemma `aggregate_triangle_poincare`
(`T ≤ λ₂fᵀDf`) is *not* bypassed.

## What regime (i) actually needs (weaker than aggregate Poincaré)

From the slack identity, regime (i) direct B is

> `RHS − T = Open + Cov_L(d,f²) − λ₂S²/m ≥ 0`,  i.e.  **`Open + 𝒜 ≥ λ₂S²/m`**,

which is *weaker* than aggregate Poincaré `Open + 𝒜 ≥ λ₂fᵀAf` (since `λ₂S²/m ≤ λ₂fᵀAf` in regime
(i)). So regime (i) does **not** require the full aggregate Poincaré — only `Open + 𝒜 ≥ λ₂S²/m`. But
this is still nontrivial: `𝒜 = Cov_L(d,f²) < 0` typically, so it is *not* implied by `Open ≥ 0`
alone. The proposed shortcut conflated "weaker than AP" with "free from `Open`"; only the former is
true.

## Conclusion

- **TASK 3 is false:** `A2_diag ≤ RHS` holds on `20/277` regime-(i) graphs. `A2_diag − RHS =
  λ₂S²/m − Cov_L(d,f²)`, and `Cov_L` is mostly negative, so `A2_diag` overshoots `RHS`. `Open` is
  load-bearing (median `1.54×` the lift slack) and cannot be discarded.
- **Regime (i) is genuinely easier than aggregate Poincaré** (more margin; `RHS − T = −Q − Required ≥
  −Q`), reducing to `Open + 𝒜 ≥ λ₂S²/m` — but this is still a nontrivial signed inequality, not a
  consequence of `Open ≥ 0`. Aggregate Poincaré (or this weaker variant) remains the open step.
- **Regime (ii)** `B` holds with margin (`T/RHS ≤ 0.83`), via the TYPE A/B bottleneck mechanisms.
- **The bypass does not eliminate `aggregate_triangle_poincare`.** The honest reduction is: regime
  (i) ⟸ `Open + 𝒜 ≥ λ₂S²/m` (weaker than AP, still open); regime (ii) ⟸ TYPE A block gap (Paper16,
  mostly formalised) + TYPE B `T = O(λ₂²)`.

## Exact identities (no new Lean lemma)
The three slack identities above are exact, but each is an immediate rearrangement of already-
formalised pieces: `degAssort_covariance` (`𝒜 = Cov_L(d,f²)`), the `A²` master identity
`T + Open = Σ[σ_v−(d_v−λ₂)²]f_v²`, and `degLin`/`degQuad` (`S`, `fᵀDf`). No new standalone identity
is introduced this round (the result is a refutation of the bypass strategy, not a new identity).
