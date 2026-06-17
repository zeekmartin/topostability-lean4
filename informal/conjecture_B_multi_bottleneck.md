# Conjecture B — multi-bottleneck stress test: the carrier mechanism BREAKS

Goal: try to break the carrier-surplus mechanism on adversarial multi-bottleneck graphs.
`surplus_c = λ₂mass_c − energy_c`; `Deficit = Σ_c surplus_c = λ₂fᵀDf − T`; `Required =
λ₂(λ₂+S²/m−fᵀDf)`; `B ⟺ Deficit ≥ Required`; carriers `H = {v : f_v² ≥ 1/(2n)}`,
`CSurplus(v) = (A·surplus)_v`. Code:
[`conjecture_B_multi_bottleneck.py`](../conjecture_B_multi_bottleneck.py).

**Headline (honest): the carrier-surplus mechanism does NOT survive — lollipops break it.**
B itself holds on **33/33** graphs and the **regime split by `sign(Required)` is valid**, but
the *carrier-surplus accounting* `Σ_H CSurplus ≥ Required` **fails on path-bottleneck
(lollipop) graphs** (`ΣCS = 0.074 < Required = 0.095`), because there the Fiedler mass and
the triangle structure are **spatially separated**. So carrier surplus is **not** a general
proof skeleton — it is specific to *vertex* bottlenecks (deg2+dense), where mass and
triangles coincide.

---

## TASK 1/2 — B holds everywhere; `Required > 0` is rare

`B` (`T ≤ RHS`) holds on **33/33** constructed graphs. **`Required ≤ 0` on 29/33** — including
**all the clique-based multi-bottleneck families** (double/`k`-bottleneck, disjoint, barbell,
appendices, caterpillar, random+planted). `Required > 0` appears **only on lollipops**
(`K_m` + a path), 4/33.

| family | `Required` |
|---|---|
| double / `k`-bottleneck on `K_m` (`k`=2,3,5,10) | **< 0** (−0.04 … −0.20) |
| disjoint bottlenecks, barbell, appendices, caterpillar | **< 0** (−0.2 … −1.9) |
| random ER + planted deg-2 | **< 0** |
| **lollipop `L=5`** | **+0.16, +0.20** |
| **lollipop `L=10`** | **+0.10, +0.13** |

So *multi-vertex bottlenecks on cliques are all `B`-trivial* (`Required ≤ 0`); only a **path
bottleneck** (lollipop) produces `Required > 0` here. (Recall deg2+dense — a dense but
*non-complete* background — also gives `Required > 0`.)

## TASK 3/4/6 — the carrier mechanism FAILS on lollipops

| lollipop | `#H` | massH | Deficit | Required | Def/Req | ΣCS | **ΣCS/Req** |
|---|---|---|---|---|---|---|---|
| `L=5`, n=50 | 5 | 0.91 | 0.439 | 0.159 | 2.76 | 0.236 | 1.48 |
| `L=5`, n=100 | 5 | 0.96 | 0.450 | 0.196 | 2.30 | 0.233 | 1.19 |
| **`L=10`, n=50** | 8 | 0.83 | 0.206 | 0.095 | 2.16 | 0.074 | **0.78 → fails to 0.78** |
| **`L=10`, n=100** | 9 | 0.92 | 0.216 | 0.125 | 1.73 | 0.075 | **0.60 (FAIL)** |

`B` holds with comfortable margin (`Def/Req = 1.7–2.8`), **but `Σ_H CSurplus < Required` on
lollipop `L=10`** — the carrier-surplus lower bound is too weak. 2/4 `Required>0` cases fail.

## Why it breaks — mass/triangle separation (diagnostic on lollipop `L=10`, n=50)

| quantity | clique part | path part |
|---|---|---|
| Fiedler mass `Σ f²` | 0.16 | **0.84** |
| apex surplus `Σ surplus_c` | **0.165** | 0.040 |

- The **Fiedler concentrates on the path** (mass 0.84, spread over the path vertices), so all
  **carriers `H` lie on the path**.
- But the **surplus lives on the clique apices** (0.165 of the 0.206 Deficit) — that is where
  the triangles are. The clique apices are **not adjacent to any path carrier** (except the
  one attachment vertex), so `CSurplus = Σ_{c∈N(carrier)} surplus_c` **misses 0.165 of the
  surplus** (exactly the "surplus on apices not adjacent to any carrier").

So **the mechanism works only when the Fiedler mass and the triangle-rich region coincide**
(deg2+dense: the bottleneck vertex's neighbours *are* the dense triangle apices). A lollipop
**separates** them — mass on the path, triangles in the clique — and the carrier-neighbour
sum cannot reach the surplus. The mechanism is genuinely **not universal**.

## TASK 5 — interference

On lollipops the carriers do share neighbours (`shared = 3–7`), so `ΣCS` double-counts some
path apices — yet it still *under*-counts the Deficit, because the missing mass is on the
clique, not in the shared path apices. Double-counting neither rescues nor explains the gap.

## TASK 7 — what survives

| regime | count | claim | holds? |
|---|---|---|---|
| `Required ≤ 0` | 29/33 | `Deficit ≥ 0` (aggregate Poincaré) ⇒ B | **yes (all)** |
| `Required > 0` | 4/33 | `Σ_H CSurplus ≥ Required` (carrier mechanism) | **NO (2 fail)** |

- **Regime (i) is robust:** `Required ≤ 0 ⇒ B` from `Deficit ≥ 0` alone, on all 29 graphs
  (and it is exactly the regime of every clique-multi-bottleneck).
- **Regime (ii) is NOT closed by carrier surplus:** the accounting fails on lollipops.
  However the underlying `Deficit ≥ Required` still holds there with margin `1.7–2.8`.

---

## Synthesis — the mechanism is broken, but B and the split survive

The stress test achieved its goal: **it broke the carrier-surplus mechanism.** Concretely:

- **`B` (= `Deficit ≥ Required`) is robust** — 33/33, with margin `≥ 1.7` even in the
  `Required > 0` cases.
- **The regime split by `sign(Required)` is exact and useful:** `Required ≤ 0` (the vast
  majority, all clique families) gives `B` for free from the aggregate Poincaré `T ≤ λ₂fᵀDf`.
- **But the carrier-surplus decomposition is *not* a general proof of the `Required > 0`
  regime.** It assumes the surplus sits in the neighbourhoods of the Fiedler-mass carriers;
  this is true for *vertex* bottlenecks (deg2+dense) but **false for path bottlenecks**
  (lollipops), where mass (path) and triangles (clique) are separated.

**Revised picture for a proof.** Regime (i) is solid (aggregate Poincaré, built on the
formalized apex identity). Regime (ii) needs a **global** lower bound on `Deficit` that does
not localise to carrier neighbourhoods — e.g. directly bounding `Deficit = λ₂fᵀDf − T` using
that `T` is small wherever `f` is large (path: no triangles; clique: `f` small), rather than
attributing surplus to carriers. The carrier mechanism is a *special-case* heuristic, not the
general lever; the general lever remains the **`Deficit ≥ Required` margin** (stable `≥ 1.7`)
plus the **`sign(Required)` split**.

### Caveats
`λ₂`, `f`, per-apex energies numerical. 8 adversarial families, `n` up to ~200; `Required > 0`
realised only on lollipops among them. `B` and the regime split are robust; the carrier
mechanism's failure on lollipops is reproducible at both sizes. The deeper invariant
(`Deficit ≥ Required`, margin `≥ 1.7`) holds throughout but is *not* explained by carrier
surplus in the separated-structure case.
