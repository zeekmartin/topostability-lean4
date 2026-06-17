# Conjecture B — the normalized factorization: a valid lower bound that does not separate

**Target.** Establish `λ₂(G[B]) ≥ c·λ₂(G)` (p=80% block) via the factorization
`λ₂(G[B]) ≈ δ_B · λ₂_norm(G[B])`, splitting the gap into degree scale `× ` normalized
expansion. Code:
[`conjecture_B_normalized_block_factor.py`](../conjecture_B_normalized_block_factor.py).
Corpus: 1962 `Required > 0` graphs.

**Headline (mixed).** The factorization is a **rigorous valid lower bound** — `λ₂(G[B]) ≥
δ_B·λ₂_norm(G[B])` holds on **100%** of graphs, so `product := (δ_B/λ₂_G)·λ₂_norm_B ≤
actual_ratio` always, and `product > 1` on **100%** (min **1.591**), `≥ 2` on 99%. So it
certifies `ratio > 1` universally. **But it does not cleanly separate:** `norm_gap ≥ 0.38` is
**false** (min 0.013, holds only 78.5%). The product stays `> 1` by a **compensation** between
the two factors, not by independent bounds — the worst cases (lollipop path-stub blocks) have a
*tiny* normalized gap (0.013) offset by a *huge* degree scale (≈120). So the "`degree_scale ≥
2.65` × `norm_gap ≥ 0.38`" decomposition fails; the residual is a **joint** product bound.

---

## The factorization quantities

| quantity | min | median | max |
|---|---|---|---|
| `degree_scale = δ_B/λ₂_G` | 2.645 | 15.7 | 297 |
| `norm_gap = λ₂_norm(G[B])` | **0.013** | 0.786 | 1.08 |
| `product = degree_scale · norm_gap` | **1.591** | 8.62 | 284 |
| `actual_ratio = λ₂_B/λ₂_G` | 2.511 | 10.8 | 295 |

| claim | result |
|---|---|
| `λ₂_B ≥ δ_B·λ₂_norm_B` (factorization valid) | **100.0%** |
| `product ≤ actual_ratio` (⇒ valid lower bound) | **100.0%** |
| `product > 1` | **100.0%** (min 1.591) |
| `product ≥ 2` | 99.0% |
| `norm_gap ≥ 0.38` | **78.5%** (min 0.013) ✗ |

**The factorization is a genuine lower bound** (`λ₂(G[B]) ≥ δ_B·λ₂_norm(G[B])`, 100%), so it
*rigorously* reduces `ratio ≥ c` to `δ_B·λ₂_norm_B ≥ c·λ₂_G`. And the product is `> 1`
everywhere, certifying `ratio > 1`. The catch is in how the product stays above 1.

## Why it does not separate — the compensation

`norm_gap` is **not** bounded below by 0.38; it drops to **0.013**. The smallest-product cases:

| family | `|B|` | `degree_scale` | `norm_gap` | `product` | `actual_ratio` | density | conductance |
|---|---|---|---|---|---|---|---|
| lollipop | 18 | 121.9 | 0.013 | 1.591 | 4.21 | 0.18 | 0.04 |
| lollipop | 15 | 78.8 | 0.021 | 1.670 | 4.24 | 0.23 | 0.06 |
| lollipop | 18 | 127.8 | 0.013 | 1.671 | 4.17 | 0.15 | 0.04 |
| lollipop | 17 | 111.2 | 0.015 | 1.679 | 4.40 | 0.19 | 0.05 |

The lowest-5%-product graphs are **65 lollipops** + 26 deg2dense + 7 others. **All worst cases
are path-stub blocks:** at p=80% the lollipop block is the clique *plus a short path stub*, and
the stub is an internal bottleneck — so `λ₂_norm(G[B]) ≈ 0.013` (the block itself is barely
connected in the normalized sense). The gap survives only because `λ₂_G` is *even smaller*
(`≈ 0.01`), making `degree_scale = δ_B/λ₂_G ≈ 120`. **The product is bounded below by
compensation:** small `norm_gap ⟺ large degree_scale`, their product `≈ 1.6`. Neither factor is
individually bounded away from its bad limit.

Note the factorization is **lossy on lollipops**: `product ≈ 1.6` while `actual_ratio ≈ 4.2`
(`λ₂_B` exceeds `δ_B·λ₂_norm_B` by `~2.6×` here). So the certified margin (1.59) is well below
the true floor (2.51), and for *longer* path stubs the product may degrade toward 1 — it is
**not** robustly bounded away from 1 the way `actual_ratio ≥ 2.51` is.

## What governs `norm_gap`

| predictor | corr with `norm_gap` |
|---|---|
| **conductance (sweep)** | **+0.965** |
| degree regularity `δ_B/Δ_B` | +0.838 |
| transitivity | −0.556 |
| clustering | −0.288 |
| internal density | −0.099 |

`norm_gap = λ₂_norm(G[B])` is governed by **conductance** (Cheeger), as it must be: the check
`cond²/2 ≤ norm_gap ≤ 2·cond` holds **100%**, median `norm_gap/cond = 1.68`. Degree regularity
is the second predictor (a near-regular block has `λ₂_norm` near 1). Density, clustering, and
triangle structure are *not* predictive (corr `≤ 0.1` for density). So `norm_gap` is precisely
the *internal conductance* of the block — and that is small exactly when the block retains a
bottleneck (lollipop path stub), which is the failure mode of the separation.

---

## Synthesis — a valid bound, an open joint inequality

- **Positive:** the factorization `λ₂(G[B]) ≥ δ_B·λ₂_norm(G[B])` holds on **all 1962** graphs,
  rigorously reducing the block lemma to `δ_B·λ₂_norm_B ≥ c·λ₂_G`. The product is `> 1`
  universally (min 1.591), so the gap `ratio > 1` is *certified* (given the factorization
  inequality). `degree_scale ≥ 2.645` is clean (prior round).
- **Negative:** the two factors do **not** separate. `norm_gap` is not bounded below by 0.38
  (min 0.013) — the lollipop path-stub blocks have near-zero internal conductance, compensated
  by a huge degree scale. So there is no "`δ_B/λ₂_G ≥ 2.65` AND `λ₂_norm_B ≥ 0.38`" proof; the
  closing inequality is irreducibly **joint**: `δ_B · λ₂_norm(G[B]) ≥ c · λ₂(G)`.
- **The joint inequality, unpacked.** Since `λ₂_norm(G[B]) ≈ h(B)` (conductance, corr 0.965),
  the target is `δ_B · h(B) ≳ c · λ₂(G)`. The quantity `δ_B · h(B)` is essentially the
  *combinatorial isoperimetric number* of `B` (`min |∂S|/|S|`, since `vol ≈ δ_B·|S|`), i.e. the
  combinatorial edge-expansion of the block. So the lemma becomes:

  > **The carrier-complement block `B` has combinatorial edge-expansion `≥ c·λ₂(G)`** — its
  > sparsest cut, measured in raw edges (not volume-normalized), exceeds the global `λ₂(G)`.

  This is the honest residual: not a degree bound, not a normalized-conductance bound, but the
  **raw edge-expansion** of `B`, which couples degree scale and conductance exactly as the data
  demands. For lollipops it holds because the block's sparsest cut (the path stub, `|∂S| ≈ 1`)
  still has `|∂S|/|S| ≳ λ₂(G) ≈ 1/L²`; for deg2+dense because the dense block has expansion
  `~ qn ≫ λ₂(G) ≈ 2`.

**Status.** The block lemma is reduced — rigorously, via the 100%-valid factorization — to a
single edge-expansion inequality on `B`. The factorization does not by itself close the lemma
(the product margin 1.59 is corpus-limited and not robustly bounded away from 1), but it
correctly identifies the closing quantity as `δ_B · λ₂_norm(G[B]) =` (essentially) the
combinatorial edge-expansion of the carrier-complement.

### Caveats
`λ₂`, `λ₂_norm`, `f` numerical; corpus = 1962 `Required > 0` graphs. The factorization
inequality `λ₂_B ≥ δ_B·λ₂_norm_B` holds on all 1962 (it is plausibly the known-type bound
`λ₂(L) ≥ δ·λ₂(L_norm)`, but is asserted here **empirically**, not proved). `product > 1` (min
1.591) and `product ≤ actual_ratio` are exact per-graph. `norm_gap`–conductance correlation
0.965 with Cheeger bounds verified 100%. Clustering/transitivity computed for blocks with
`|B| ≤ 80` (n=1360). The worst-case product (1.591) is corpus-limited; longer lollipop stubs
may push it toward 1, so the factorization certifies `ratio > 1` on the corpus but is not a
proof of a uniform `c > 1`.
