# Conjecture B — Required vs block-gap: the threshold can be avoided entirely

Quantify `Required` against the block gap `ratio = λ₂(G[B])/λ₂(G)`, and decide whether a
regime split at some `ε` is needed. Code:
[`conjecture_B_final_threshold.py`](../conjecture_B_final_threshold.py). Corpus: the 1962
`Required > 0` graphs. Two blocks compared: **`m`** `= {d_v ≥ median}` (degree-median),
**`p`** `=` complement of the smallest carrier set holding 80% of `‖f‖²` (p=80%
Fiedler-complement).

**Headline.** **No threshold is needed if we use the `p=80%` block.** Across all 1962 graphs,
`ratio_p ≥ 2.51` **unconditionally** (no graph has `ratio_p < 2`), so the block gap is bounded
below by `≈ 2.5·λ₂(G)` everywhere — including the `Required → 0⁺` boundary. The degree-median
block fails to be threshold-free (`ratio_m` is **non-monotone** in `Required`: the small-Required
regime is bimodal), and would need a split at `ε ≈ 0.02–0.05`. Bonus: `Deficit/Required ≥
1.374` **always** — B holds with `≥ 37%` margin on every graph.

---

## TASK 1 — Required vs ratio

| boundary | value |
|---|---|
| largest `Required` with `ratio_m < 2` (degree-median) | **0.0178** |
| smallest `Required` with `ratio_m ≥ 3` | 0.0001 |
| largest `Required` with `ratio_p < 2` (p=80%) | **0.0000 (none)** |
| smallest `Required` with `ratio_p ≥ 3` | 0.0001 |

Binned by `Required` (min / median of each ratio):

| `Required ∈` | `n` | `ratio_m` min / med | `ratio_p` min / med |
|---|---|---|---|
| (0, 0.01] | 48 | **1.07** / 141.6 | **3.59** / 7.36 |
| (0.01, 0.02] | 36 | **1.08** / 171.1 | 3.46 / 5.60 |
| (0.02, 0.05] | 180 | 2.64 / 1059.7 | 2.51 / 7.65 |
| (0.05, 0.10] | 201 | 2.45 / 1971.2 | 3.71 / 10.42 |
| (0.10, 0.20] | 155 | 2.74 / 406.9 | 3.33 / 6.54 |
| (0.20, 0.50] | 414 | 2.51 / 6.29 | 3.35 / 8.64 |
| (0.50, 1.00] | 544 | 2.91 / 9.01 | 4.13 / 13.80 |
| (1.00, ∞) | 384 | 3.88 / 12.43 | 5.28 / 19.90 |

**The degree-median ratio is non-monotone in `Required`** and *bimodal* at small `Required`:
the `(0, 0.01]` bin has `ratio_m` median **141** but min **1.07**. Two disjoint populations
sit at small `Required`: near-complete deg2+dense graphs (`λ₂ ≈ 2`, dense block `λ₂` huge ⇒
`ratio_m ≈ 10²–10³`) and sparse two-cycle/path graphs (`ratio_m ≈ 1`). So no clean
`Required > ε ⟹ ratio_m ≥ 2` holds below `ε = 0.018`. **The `p=80%` block removes the
bimodality:** its min over *every* bin is `≥ 2.51`, monotone-ish and bounded away from 2.

## TASK 2 — regime split at `ε` (degree-median block)

| `ε` | `n≤ε` | min `Def/Req` | min `Deficit` | `Def ≥ ε`? | `n>ε` | min `ratio_m` | min `ratio_p` | `%` dense `p` |
|---|---|---|---|---|---|---|---|---|
| 0.01 | 48 | 6.53 | 0.055 | ✓ | 1914 | 1.08 | 2.51 | 30.9% |
| 0.05 | 264 | 1.55 | 0.055 | ✓ | 1698 | 2.45 | 3.33 | 34.5% |
| 0.10 | 465 | 1.54 | 0.055 | ✗ | 1497 | 2.51 | 3.33 | 38.7% |
| 0.50 | 1034 | 1.54 | 0.055 | ✗ | 928 | 2.91 | 4.13 | 57.1% |

- **A degree-median split is clean at `ε = 0.05`:** below, `Required ≤ 0.05 < 0.055 ≤ Deficit`
  (the corpus min Deficit is 0.055), so `Deficit ≥ ε ≥ Required` ⇒ B; above, `ratio_m ≥ 2.45`.
- **But the below-`ε` branch leans on `Deficit ≥ 0.055`, which is corpus-limited.** As a graph
  approaches `K_n`, both `Required` and `Deficit → 0`, so no absolute constant lower bound on
  `Deficit` is a theorem. The split is therefore *clean on the corpus* but not yet a proof. (The
  corpus does not probe arbitrarily close to `K_n` with `Required > 0`; there `ratio_m` is
  enormous, so the block route would carry it — which is exactly the argument for dropping the
  split.) Note the density condition `δ_p ≥ (|B|−2)/2` for the *classical* gap bound holds only
  31–57% even for the `p` block, so the gap is **not** explained by the simple min-degree bound.

## TASK 3 — avoid `ε` entirely

> **YES — the `p=80%` Fiedler-complement block gives `ratio_p ≥ 2.51` for all 1962 graphs, with
> no threshold** (TASK 3b: graphs with `ratio_p < 2` = **0**; min `ratio_p = 2.51`,
> max `Required = 2.43`).

Threshold-free quantities (want bounded below by `c > 0`):

| quantity | min | median | `≥ 1` |
|---|---|---|---|
| `Required · ratio_m²` | 0.0007 | 89.0 | 97.4% |
| `Required · ratio_p²` | 0.0031 | 43.9 | 94.8% |
| `Deficit · ratio_m` | 0.0589 | 31.3 | 99.2% |
| **`Deficit / Required` (= B-margin)** | **1.374** | 3.67 | **100%** |
| `Deficit · ratio_p / Required` | 10.85 | 48.8 | 100% |
| `(Deficit/Required)·(1 − 1/ratio_p)` | 1.356 | 3.34 | 100% |

Two clean threshold-free facts:
1. **`ratio_p ≥ 2.51` unconditionally** — the gap of the `p=80%` block is bounded away from 1
   without any case split. This is the single cleanest replacement for the regime split.
2. **`Deficit ≥ 1.374·Required` unconditionally** — B is never tight (the 37% margin is bounded
   away from 0), confirming B holds robustly across the whole `Required > 0` regime.

The products `Required·ratio²` and `Deficit·ratio` are *not* bounded below (min `≈ 0.001`,
`0.06`) — they fail at small-`Required` deg2dense where one factor is tiny — so those are not
proof handles. The useful invariants are the two above.

## TASK 4 — formalizability of the threshold-free route

Using the `p=80%` block, the proof of B on `Required > 0` is a **single unconditional chain**,
no `ε`:

| step | statement | Lean status |
|---|---|---|
| 1 | `(L_B − λ₂I)f_B = g`, `g_v = Σ_{u∼v,u∉B}(f_u − f_v)` | exact (residual `1e-13`); algebraic, **formalizable** |
| 2 | Poincaré-on-block `‖f_B − mean‖² ≤ ‖g‖²/(γ − λ₂)²` | spectral decomposition of `L_B`; **formalizable** (needs eigenbasis sum; Mathlib has symmetric-operator eigendecomposition) |
| 3 | `γ = λ₂(G[B]) ≥ 2.51·λ₂(G)` | **the open gap** — *not* the classical `2δ−|B|+2` (block dense only 31–57%); needs a conductance/Cheeger argument relating the carrier-cut to `λ₂(G)` |
| 4 | uniform `f_B` ⇒ deg2+dense (mass) / lollipop (`T`) mechanism ⇒ B | the two closed families |

**Steps 1–2 are formalizable now** (algebra + spectral decomposition); **step 4** is the two
closed families. **Step 3 is the sole remaining analytic obstruction**, and the threshold-free
finding sharpens it precisely: prove `λ₂(G[B_{p=80\%}]) ≥ c·λ₂(G)` with `c ≈ 2.5`,
unconditionally. The natural tool is **conductance**: `B` is the complement of the low-mass
carriers, which straddle the bottleneck where `λ₂(G)` is small; the bulk `B` has higher
internal conductance, hence higher `λ₂(G[B])`. This replaces the regime split with one clean
spectral-geometry lemma.

---

## Synthesis

- **The regime split is avoidable.** The `p=80%` Fiedler-complement block has `ratio ≥ 2.51`
  on all 1962 `Required > 0` graphs — no `ε`. The degree-median block is non-monotone (bimodal
  at small `Required`) and would need `ε ≈ 0.02–0.05` with a corpus-limited `Deficit ≥ 0.055`
  argument below it; the `p=80%` block makes that unnecessary.
- **B is never tight:** `Deficit ≥ 1.374·Required` everywhere (37% margin, threshold-free).
- **The proof reduces to one unconditional lemma:** `λ₂(G[B_{p=80\%}]) ≥ c·λ₂(G)`, `c ≈ 2.5`.
  With it, Poincaré-on-block (rigorous, step 2) forces `f_B` uniform and the two closed-family
  mechanisms finish. Steps 1, 2, 4 are in hand; step 3 (a conductance bound on the bulk block)
  is the final target.

### Caveats
`λ₂`, `f` numerical; corpus = 1962 `Required > 0` graphs (deg2+dense `n∈{50..1000}`,
lollipops, 1949 random seed-7). `ratio_p ≥ 2.51` and `Deficit/Required ≥ 1.374` are **empirical
over this corpus** (not proved); the corpus does not probe arbitrarily close to `K_n` with
`Required > 0`. Steps 1–2 of the chain are exact/rigorous (verified prior round); the gap bound
(step 3) and the conductance argument are conjectural. The `p=80%` threshold itself is a choice;
`p ∈ [70%, 90%]` all give min ratio `≈ 2.5` (round `canonical_detector`).
