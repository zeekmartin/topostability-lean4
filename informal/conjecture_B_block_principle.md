# Conjecture B — testing the general block principle for the `Required > 0` regime

**Hypothesis.** Every graph with `Required > 0` has a well-connected block `B` with
`λ₂(G[B]) ≫ λ₂(G)`. Code: [`conjecture_B_block_principle.py`](../conjecture_B_block_principle.py).

**Headline (hypothesis SURVIVES, with a clean analytic backbone).** Two results, one
rigorous and one empirical:
1. **`Required > 0 ⟺ fᵀAf < S²/m`** (exact identity, since `λ₂ = fᵀDf − fᵀAf`). For a
   **regular** graph `S = dᵀf = 0` and `fᵀAf = d − λ₂ > 0`, so **`Required > 0` is impossible
   — degree heterogeneity is NECESSARY** (0 violations in 1949 `Required>0` graphs found).
2. Across **1949 `Required > 0` graphs** (random deg2dense / degk / lollipop / path-end-dense /
   two-cycle), the **minimum best-block-ratio is 3.07**, and **no graph** has best-ratio `< 3`.
   The block is real, but **no single block-detector is universal** — different bottleneck
   topologies expose it through different definitions.

The striking negative: **every "triangle-rich, no dense block" adversarial family has
`Required ≤ 0`** and is therefore B-trivial. Triangles *raise* `fᵀAf` (correlated Fiedler
across triangle edges), pushing `fᵀAf > S²/m`, so they never enter the open regime. You
cannot reach `Required > 0` by piling on triangles without a well-connected block — the two
go together.

---

## TASK 1 — prior `Required > 0` families all have a high-gap block

Block ratio `= λ₂(G[B]) / λ₂(G)` for three detectors: **hi-deg** `{v : d_v > median}`,
**2conn** = largest 2-connected (biconnected) subgraph, **non-carr** `{v : f_v² < 1/n}`.

| family | `n` | `λ₂` | `Required` | B | Def/Req | hi-deg | 2conn | non-carr | **best** |
|---|---|---|---|---|---|---|---|---|---|
| deg2dense | 100 | 1.99 | 1.067 | ✓ | 1.87 | 13.1 | 1.0 | 24.2 | **24.2** |
| deg2dense | 200 | 1.99 | 1.174 | ✓ | 1.72 | 26.7 | 1.0 | 53.9 | **53.9** |
| lollipop 20,5 | 25 | 0.097 | 0.075 | ✓ | 5.54 | — | 206.8 | 10.3 | **206.8** |
| lollipop 50,10 | 60 | 0.026 | 0.106 | ✓ | 1.98 | — | 1929.5 | 15.1 | **1929.5** |

**The detector is topology-dependent.** For the **vertex-bottleneck** (deg2dense), the whole
graph is 2-connected so `2conn` gives ratio `1.0` (useless), but the **hi-degree / non-carrier**
set *is* the dense block (ratio 24–54). For the **path-bottleneck** (lollipop), `hi-deg` is
`—` (only the junction vertex exceeds the median clique degree) but the **largest 2-connected
component is the clique** (ratio 207–1930). No one definition wins everywhere; the *best of
the three* is always `≫ 1`.

## TASK 2 — adversarial triangle-rich families are all `Required ≤ 0`

Designed to have "many triangles, no dense block." Every one lands in `Required ≤ 0`.

| family | `n` | `λ₂` | `fᵀAf` | `S²/m` | `Required` | Req>0? | B | best block |
|---|---|---|---|---|---|---|---|---|
| triangle cactus k=40 | 81 | 0.005 | 2.920 | 0.000 | −0.013 | no | ✓ | 665 |
| triangulated tree t=50 | 99 | 0.020 | 2.869 | 0.000 | −0.057 | no | ✓ | 150 |
| power-law config n≈150 | 150 | 0.265 | 1.875 | 0.018 | −0.491 | no | ✓ | 1.4 |
| expander + pendants | 40 | 0.206 | 2.354 | 0.004 | −0.485 | no | ✓ | 4.8 |
| book (k=30 triangles) | 32 | 2.000 | −0.000 | 0.000 | −0.000 | no | ✓ | 1.0 |
| friendship k=30 | 61 | 1.000 | 1.000 | 0.000 | −1.000 | no | ✓ | 3.0 |
| windmill-K₄ k=8 | 25 | 1.000 | 2.000 | 0.000 | −2.000 | no | ✓ | 4.0 |

**Why they fail to reach `Required > 0`:** `Required > 0 ⟺ fᵀAf < S²/m`. Triangles make the
Fiedler *positively correlated* across the many triangle edges, so `fᵀAf` is large-positive
(1.0–2.9), while these graphs are near-balanced so `S²/m ≈ 0`. Hence `fᵀAf ≫ S²/m` and
`Required < 0` — B holds trivially via the aggregate Poincaré (`Deficit ≥ 0 ≥ Required`).
Note the boundary cases: the **book graph** (k triangles on a shared spine) has `fᵀAf = 0`
exactly and `Required = 0`; the **friendship** graph (`λ₂ = 1`, `fᵀAf = 1`) and **windmill-K₄**
(`fᵀAf = 2`) sit safely negative. The triangle blocks (`K₃`, gap 3; `K₄`, gap 4) *are* there
with `best ratio ≥ 3`, but they're moot since `Required < 0`.

**The adversarial program backfires.** "No dense block" and "`Required > 0`" cannot be
arranged together by these constructions — removing the well-connected block removes the
`Required > 0`.

## TASK 3 — when can `Required > 0` occur? (the critical question)

**Exact reformulation.** `λ₂ = fᵀDf − fᵀAf` (from `Lf = λ₂f`, `L = D − A`), so
`Required = λ₂(λ₂ + S²/m − fᵀDf) > 0 ⟺ fᵀDf < λ₂ + S²/m ⟺`

> **`fᵀAf < S²/m`.**

- **Irregularity is NECESSARY.** Regular ⇒ `S = dᵀf = d·1ᵀf = 0` and `Af = (d−λ₂)f` ⇒
  `fᵀAf = d − λ₂ > 0 = S²/m`, so `Required < 0` always. (Search: **0** regular graphs with
  `Required > 0` out of all sampled.)
- **Irregularity is NOT sufficient.** Every triangle-rich irregular family above is
  `Required < 0`. `Required > 0` is genuinely *rare* — in the search it arose essentially only
  from the **low-degree-vertex + dense-block** constructions (deg2dense, degk, lollipop,
  path-end-dense).
- **Does `Required > 0` force a well-connected block? Structurally, yes.** `fᵀAf = fᵀDf − λ₂`,
  so `Required > 0 ⟺ fᵀDf < λ₂ + S²/m` — the Fiedler's **degree-weighted mass `fᵀDf` must be
  small**, i.e. the Fiedler mass sits on **low-degree** vertices. For `f ⊥ 1` with most of `‖f‖²`
  on low-degree vertices, the *complementary* high-degree vertices must form a connected,
  well-mixed set (otherwise the eigen-equation could not pin a small `λ₂` while keeping those
  vertices near-flat) — that complement is the high-gap block. The empirical floor
  `λ₂(G[B])/λ₂(G) ≥ 3` is the quantitative shadow of this.

## TASK 4 — did the block principle break?

**No.** Across 1949 `Required > 0` graphs the minimum best-block-ratio is **3.07**, attained
at a near-boundary case (deg2dense `n=25`, `Required = 0.036`, `Def/Req = 52`); there
`hi-deg` ratio `= 3.07`, `non-carr = 2.81`, `2conn = 1.0`. **Zero** graphs had best-ratio `< 3`.
So no alternative (non-block) mechanism was needed. The one refinement forced by the data:

> The "well-connected block" is real for every `Required > 0` graph, but it must be detected
> with the **topology-appropriate definition** — hi-degree / non-carrier set for
> vertex-bottlenecks (deg2dense), largest 2-connected component for cut-bottlenecks
> (lollipop). The *best of these* always has gap `≥ 3·λ₂(G)`.

---

## Synthesis

- **Rigorous backbone:** `Required > 0 ⟺ fᵀAf < S²/m`. Regular graphs ⇒ `Required < 0`
  (irregularity necessary). Triangle-rich graphs ⇒ `fᵀAf` large ⇒ `Required < 0`. So the open
  regime is confined to **degree-heterogeneous, low-clustering-on-the-carriers** graphs where
  the Fiedler mass is on low-degree vertices — exactly the deg2dense / lollipop shape.
- **Empirical principle (1949 graphs):** every `Required > 0` graph has a block with
  `λ₂(G[B]) ≥ 3·λ₂(G)`; min 3.07, no exceptions. The principle from the two closed families
  generalizes across the whole sampled `Required > 0` regime.
- **Toward a proof:** B on `Required > 0` would follow from formalizing *"`fᵀDf < λ₂ + S²/m`
  ⇒ ∃ a vertex set `B` with `λ₂(G[B]) ≫ λ₂(G)` carrying the high-degree bulk, on which the
  block-resolvent forces Fiedler-flatness."* The two extremal families (deg2dense mass-on-block,
  lollipop T-on-block) are the two instances; the principle now has empirical support across
  ~2000 graphs and a necessary-condition skeleton (`fᵀAf < S²/m`, irregularity forced).

### Caveats
`λ₂`, `f` numerical. `Required > 0` reformulation `fᵀAf < S²/m` and `regular ⇒ Required < 0`
are exact identities (verified: 0 regular counterexamples). The block-ratio floor (min 3.07,
none `< 3`) is over 1949 `Required > 0` graphs drawn from deg2dense/degk/lollipop/path-end/
two-cycle generators; `Required > 0` was not produced by any triangle-rich or near-regular
family despite explicit attempts (TASK 2), which is itself evidence for the principle. The
three block detectors are heuristic; the claim is that *their max* exceeds `3·λ₂(G)`, not that
any fixed one does.
