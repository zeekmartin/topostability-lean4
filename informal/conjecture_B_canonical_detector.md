# Conjecture B — the canonical Fiedler-complement block detector

For the open `Required > 0` regime, find a *single, canonical* rule that exhibits the
well-connected block whose gap forces B. Detector: sort vertices by `f_v²` descending; the
carriers `C_p` are the smallest set holding `p%` of `‖f‖²`; the block is `B =` largest
connected component of `G[V \ C_p]`. Code:
[`conjecture_B_canonical_detector.py`](../conjecture_B_canonical_detector.py).

**Headline.** The detector works: on the full `Required > 0` corpus (deg2+dense sweep,
lollipops, and the 1949 random graphs from the block round — **1962** graphs total),
`ratio = λ₂(G[B])/λ₂(G) ≥ 2.5` **universally**, and `≥ 3` for **1960/1962 = 99.9%**, with the
block **always connected**. The two sub-3 cases (`ratio 2.51, 2.81`) are near the
`Required = 0` boundary (`Req ≈ 0.03`) and still `≫ 1`. **Threshold `p = 80%` is the most
reliable** single rule (99.9% `≥ 3`, min 2.51, 100% connected). A **degree-median** detector
`{v : d_v ≥ median}` is simpler and nearly as good (98.1% `≥ 3`). Block uniformity holds as an
*asymptotic* mechanism (tightens with the gap) but **not** as a finite-`n` guarantee — the
`std/|mean| < 0.1` test is finite-size sensitive.

---

## TASK 1 — the detector on the two canonical families

`rat / conn / unif` = `ratio` / connected? / `std(f|_B)/|mean(f|_B)|`, at three thresholds:

| family | `n` | `λ₂` | p=50% | p=80% | p=90% |
|---|---|---|---|---|---|
| deg2dense | 50 | 1.98 | 10.8/Y/0.31 | 10.8/Y/0.31 | 10.8/Y/0.31 |
| deg2dense | 200 | 1.99 | 53.9/Y/0.16 | 53.9/Y/0.16 | 53.9/Y/0.16 |
| deg2dense | 1000 | 2.00 | 294.1/Y/0.07 | 294.1/Y/0.07 | 294.1/Y/0.07 |
| lollipop (20,5) | 25 | 0.097 | 2.3/Y/2.68 | 10.3/Y/0.48 | 113.8/Y/0.03 |
| lollipop (50,10) | 60 | 0.026 | 2.5/Y/2.76 | 8.0/Y/0.76 | 38.6/Y/0.22 |
| lollipop (30,20) | 50 | 0.009 | 2.1/Y/2.23 | 6.5/Y/0.81 | 8.1/Y/1.33 |

**Two regimes, visible in the threshold-dependence:**
- **deg2+dense (vertex bottleneck): `p`-independent.** The single bottleneck vertex `v₀`
  carries `> 90%` of `‖f‖²`, so `C_p = {v₀}` for every `p` and `B =` the dense block always.
  `ratio = λ₂(dense)/λ₂ ≈ qn/2` grows with `n` (10.8 → 294), and block uniformity tightens
  (`0.31 → 0.07`).
- **lollipop (path bottleneck): higher `p` essential.** The Fiedler mass is spread along the
  path, so a low threshold leaves path remnants in `B` (ratio `≈ 2`, non-uniform); `p = 90%`
  strips the path down to the **pure clique** (ratio `38–114`, uniform `0.03–0.22`). For the
  long path `(30,20)` even `p = 90%` leaves a path stub, capping the ratio at 8.1.

## TASK 2 — universal reliability across 1962 `Required > 0` graphs

| `p` | min ratio | median | `%≥3` | `%connected` |
|---|---|---|---|---|
| 50% | 1.84 | 8.86 | 73.3% | 100% |
| 70% | 2.51 | 9.09 | 99.5% | 100% |
| **80%** | **2.51** | **10.83** | **99.9%** | **100%** |
| 90% | 2.51 | 13.37 | 99.9% | 100% |

> **best-over-`p` ratio: min = 2.51, median = 13.37, `≥ 3` for 1960/1962 (99.9%).**

Only **2** graphs fall below 3 (both near the `Required = 0` boundary):
`n=25, λ₂=1.948, Req=0.0355, best=2.81` and `n=28, λ₂=1.890, Req=0.0297, best=2.51`. So the
honest universal floor is **`ratio ≥ 2.5`** (not 3), with `≥ 3` for all but the two
near-boundary cases. **`p = 80%` is the most reliable single threshold:** it matches the
best-over-`p` reliability (99.9% `≥ 3`), keeps the block connected on every graph, and — unlike
`p = 50%` (only 73% `≥ 3`) — is robust to path-bottleneck spreading. Higher `p` gives larger
median ratios but the same floor.

## TASK 3 — degree-based detectors

| detector | min | median | `%≥3` |
|---|---|---|---|
| `{v : d_v ≥ median}` | 1.07 | 10.88 | **98.1%** |
| `{v : d_v ≥ λ₂}` | 1.00 | 1.00 | 0.0% |

- **`deg ≥ median` is simpler and almost as good** (98.1% vs 99.9%, same median ≈ 10.9). It
  needs no Fiedler vector — just the degree sequence — so it is the cleaner *proof-side*
  detector. It fails slightly more often (the high-degree set can bleed across the bottleneck
  or, for lollipops, collapse to the junction vertex), which is exactly why the
  Fiedler-complement at `p = 80%` is marginally more reliable.
- **`deg ≥ λ₂` is useless** (0% `≥ 3`): `λ₂` is below the minimum degree on these graphs
  (e.g. `λ₂ ≈ 2` while `v₀` has degree 2), so the set is the whole graph and `ratio = 1`.
  This confirms the threshold must scale with the *degree distribution*, not with `λ₂`.

**Recommendation:** use `deg ≥ median` as the canonical detector for the proof (degree-only,
98% reliable); fall back to the Fiedler-complement at `p = 80%` for the residual cases.

## TASK 4 — block uniformity (proof-relevant)

The mechanism needs `f|_B` approximately uniform so that the block-resolvent argument applies
(deg2+dense: `Σ_B d_v f_v²` large; lollipop: `T` small). Measuring `std(f|_B)/|mean(f|_B)|` at
the best-ratio threshold:

| `std/|mean| <` | fraction |
|---|---|
| 0.05 | 4.9% |
| 0.10 | 6.5% |
| 0.20 | 12.9% |
| 0.50 | 76.3% |

median `= 0.350`; among **high-gap** graphs (`best ratio ≥ 20`, `n = 557`): median `= 0.209`,
`< 0.1` for 22.8%.

**The strict `< 0.1` test does not hold universally — but the mechanism does.** Two honest
caveats on the metric:
1. **Finite-size.** The block-resolvent bound is `f|_B = `const`+ O(λ₂/λ₂(B)) = `const`·(1 ±
   O(1/ratio))`; non-uniformity scales as `1/ratio`. The corpus is dominated by small graphs
   (`n = 20–120`) where `ratio` is modest, so `std/|mean|` is `O(0.1–0.5)`. On the clean large
   cases it tightens as predicted: deg2dense `n=1000 → 0.07`, lollipop short path `→ 0.03`,
   and the high-gap subset median (0.21) is well below the overall (0.35).
2. **Metric instability.** `std/|mean|` blows up when `mean(f|_B) → 0`, which happens when the
   auto-detected `B` bleeds across a Fiedler sign-change (long-path lollipops). This inflates
   the statistic without the block being non-uniform in the proof-relevant sense.

So uniformity is the correct **asymptotic** mechanism (improving monotonically with the gap
ratio), confirming the resolvent picture, but it is **not** a finite-`n` certificate at the
`< 0.1` level. The proof statement should be `f|_B = `const`+ O(1/ratio)`, not a fixed bound.

---

## Synthesis

- **Canonical detector exists and is reliable.** Fiedler-complement at `p = 80%` gives
  `λ₂(G[B])/λ₂(G) ≥ 2.5` on **all** 1962 `Required > 0` graphs, `≥ 3` on 99.9%, block always
  connected. This is the single rule that unifies the deg2+dense (vertex) and lollipop (path)
  block detections, with the threshold-dependence cleanly separating the two topologies.
- **Degree-median is the simpler proof-side detector** (98.1% `≥ 3`, degree-only).
- **The floor is `≈ 2.5`, not 3**, with two near-`Required=0` exceptions; the gap is real and
  bounded away from 1 everywhere.
- **Uniformity is asymptotic**: `f|_B` is uniform up to `O(1/ratio)`, tightening with the gap;
  the literal `std/|mean| < 0.1` holds only for large/high-gap graphs, so the proof must use
  the `O(λ₂/λ₂(B))` resolvent bound rather than a finite threshold.

This pins the remaining analytic task precisely: **show `Required > 0` ⇒ the degree-median (or
`p=80%` Fiedler-complement) block has `λ₂(G[B]) ≥ c·λ₂(G)` with `c > 1`, and that the
block-resolvent then forces `f|_B = `const`+ O(λ₂/λ₂(B))`.** The two closed families are the
two instances; the detector now makes "the block" a concrete, computable object on every
`Required > 0` graph.

### Caveats
`λ₂`, `f` numerical. Corpus = deg2+dense `n∈{50..1000}` + lollipops `(m∈{10,20,50}, L∈{3..20})`
+ 1949 random graphs (deg2dense/degk/lollipop/path-end/two-cycle, seed 7) filtered to
`Required > 0` (1962 total). Ratios use the largest connected component of `G[B_p]`. The
`≥ 2.5` floor and 99.9% `≥ 3` are over this corpus; the two sub-3 graphs are near the
`Required = 0` boundary. Uniformity statistics use `std/|mean|` (noted unstable when
`mean → 0`).
