# Conjecture B — what drives α = W/(μ₂·fᵀDf) > 1 on the 15% violators

Closely studies the 15% of graphs where the D4 candidate `W ≤ μ₂·fᵀDf` fails
(`α := W/(μ₂·fᵀDf) > 1`). Code:
[`conjecture_B_alpha_analysis.py`](../conjecture_B_alpha_analysis.py). Hard set:
1957 irregular `T(G)`-connected graphs (incl. dense Watts–Strogatz up to n=29).

**Headline.** Violations are driven by **low μ₂ + high ΣH** — *large, near-regular,
bottlenecked* graphs — **not** by degree variance. No simple correction
`W ≤ μ₂·fᵀDf·g(feature)` reaches 100%. And a closer look shows the **base
inequality `μ₂·fᵀDf ≤ R''` is itself not robust** (min ratio 0.724, i.e. it fails
by up to 38%) — the earlier "100%" was sampling-dependent. **D4 is less promising
than the prior pass suggested.**

- violators: **303/1957 = 15.5%**; `α` median **1.26** (mild), max **3.23**.

---

## 1. What predicts α? (top 3: μ₂, ΣH, density)

`corr(α, feature)`:

| feature | all graphs | violators only |
|---|---|---|
| **μ₂** (normalized gap) | **−0.710** | −0.352 |
| **ΣH** (combinatorial mass) | **+0.707** | +0.642 |
| **density** `m/C(n,2)` | **−0.677** | −0.498 |
| avg path length | +0.675 | +0.465 |
| modularity (Fiedler bisection) | +0.648 | +0.448 |
| conductance (sweep) | −0.643 | −0.502 |
| clustering | −0.590 | −0.449 |
| σ²_d (degree variance) | +0.574 | +0.149 |
| Δ/δ | +0.405 | −0.216 |
| assortativity | +0.315 | +0.331 |
| frac equal-degree edges | −0.332 | −0.087 |
| **cv² = σ²_d/d̄²** | **+0.226** | **−0.299** |

**Reading.** Large `α` ⟺ **small normalized gap μ₂**, **large combinatorial mass
ΣH**, **low density**, **long paths / high modularity / low conductance** — all the
signatures of a *large, sparse-ish, bottlenecked* graph. Critically, the
*relative* degree variance `cv²` is a **weak/negative** predictor on the violators
(`−0.30`): the violators are **near-regular**, so any degree-spread correction is
doomed (see §4). The driver is spectral–combinatorial (μ₂, ΣH), not degree-spread.

---

## 2. Correction feasibility — and a correction to the prior claim

- **Constant `g` fails:** `max α = 3.23` but `min R''/(μ₂·fᵀDf) = 0.724`. A constant
  needs `g ≥ 3.23` to fix `W ≤ g·μ₂fᵀDf`, but then `g·μ₂fᵀDf ≤ R''` holds on only
  11%. No overlap.
- **`μ₂·fᵀDf ≤ R''` is NOT 100%.** `min R''/(μ₂fᵀDf) = 0.724 < 1`, so on some
  graphs `μ₂·fᵀDf` *exceeds* `R''` by up to 38%. The "100%" reported in
  `conjecture_B_rho_lemmas.md` was sampling-dependent (smaller WS set); on the
  larger hard set it breaks. **So even a proof of `W ≤ μ₂·fᵀDf` would not by itself
  give `W ≤ R''`** — the D4 lower-proxy leaks.

---

## 3. The five worst violators — large, near-regular, bottlenecked

| α | n | m | Δ/δ | dens | clust | cv² | cond | mod | μ₂ | λ₂ | ΣH |
|---|---|---|---|---|---|---|---|---|---|---|---|
| **3.23** | 29 | 203 | 1.8 | 0.50 | 0.54 | 0.015 | 0.35 | 0.18 | 0.55 | 6.99 | 874 |
| 2.95 | 27 | 162 | 1.8 | 0.46 | 0.51 | 0.015 | 0.33 | 0.18 | 0.51 | 5.68 | 550 |
| 2.79 | 29 | 203 | 1.8 | 0.50 | 0.53 | 0.013 | 0.33 | 0.16 | 0.54 | 7.07 | 665 |
| 2.45 | 26 | 130 | 1.7 | 0.40 | 0.48 | 0.013 | 0.27 | 0.24 | 0.42 | 4.15 | 324 |
| 2.41 | 24 | 144 | 1.4 | 0.52 | 0.58 | 0.008 | 0.34 | 0.17 | 0.55 | 6.39 | 369 |

All are the **largest** graphs in the set (n=24–29), **near-regular** (`Δ/δ ≤ 1.8`,
`cv² ≤ 0.015`, degree sequences like `[16×7, 15×…]`), with **small normalized gap**
(`μ₂ ≈ 0.5`), **large ΣH** (324–874), and mild community structure (`mod ≈ 0.2`,
clustering ≈ 0.5). These are exactly Watts–Strogatz-type graphs: locally clustered,
near-regular degrees, a modest global bottleneck. The min-degree weights are small
(`Δ−δ` tiny) but spread over *many* edges (huge ΣH), while `μ₂` is small — so
`μ₂·fᵀDf` undershoots `W`.

---

## 4. Correction candidates `W ≤ μ₂·fᵀDf·g` — none closes

| `g` | `W ≤ base·g` | `base·g ≤ R''` | both |
|---|---|---|---|
| `1 + σ²_d/d̄²` (=1+cv²) | 86% | 95% | 81% |
| **`Δ/d̄`** | 93% | 93% | **86%** |
| `1 + assortativity` | 70% | 100% | 70% |
| `Δ/δ` | 97% | 69% | 66% |
| const `3.23` (=max α) | 100% | 11% | 11% |

- **`1+cv²` is useless:** the violators are near-regular (`cv² ≈ 0.01`), so the
  factor is `≈1.01` and fixes nothing — directly explaining why the natural
  degree-variance correction fails.
- **`1+assortativity` backfires:** violators are slightly *dis*assortative
  (`assort ≈ −0.05`), so `g < 1` and it tightens the wrong way.
- **`Δ/d̄` is best (86% both)** but still not universal — it helps the W-side and
  hurts the R''-side, never reaching 100% simultaneously.
- The data-driven constant fixes `W` but blows past `R''` (11%).

**No simple `μ₂`-replacement works.** Because the violators are near-regular, every
degree-spread factor (`cv²`, `Δ/δ`, `Δ/d̄`, assortativity) is either ≈1 (no help) or
overshoots `R''`. A working correction would have to depend **jointly on μ₂ and
ΣH** (the two actual drivers) — i.e. it is no longer "simple."

---

## Synthesis

1. **α>1 is a low-μ₂ / high-ΣH phenomenon** (large near-regular bottlenecked
   graphs), with density/conductance/modularity as correlated size-and-bottleneck
   proxies. Degree variance is *not* the driver (violators are near-regular).
2. **No simple feature correction closes the gap**; the best (`Δ/d̄`) reaches 86%.
   Corrections built on degree spread are structurally doomed here.
3. **The D4 lead is downgraded.** Beyond `W ≤ μ₂·fᵀDf` failing on 15.5%, the
   proxy `μ₂·fᵀDf ≤ R''` itself fails (min ratio 0.724), so the chain leaks at both
   ends. Salvaging it needs a proxy with **joint μ₂–ΣH dependence**, not a tweak.
4. **Implication.** The hard regime for Conjecture B is precise and now named:
   *large, near-regular, bottlenecked (low-μ₂, high-ΣH) graphs* — the Watts–Strogatz
   regime. Any successful bound must be tight exactly there, where degree-based and
   single-spectral-quantity arguments are weakest. The realistic next step is a
   **two-parameter (μ₂, ΣH) spectral bound**, or returning to the exact identity
   route rather than chasing a clean one-quantity proxy.

### Caveats
- `λ₂`, `μ₂`, `f` numerical; sweep conductance is the Fiedler-order proxy;
  modularity from the Fiedler sign bisection. Hard set deliberately includes large
  dense Watts–Strogatz (n≤29) to populate the violator regime. Lock `W ≤ R''` still
  holds throughout (the failures are of the *proxy*, not the lock).
