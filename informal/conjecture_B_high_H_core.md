# Conjecture B — the high-H hard core: sharper bounds, and why they still fail at scale

Target the uncovered 9% (H high, `C<0`, crude CS fails, `|C|/R″ ≤ 0.26`): find a
sharper bound `|C| ≤ B ≤ R″` to close `C+R″ ≥ 0`. Code:
[`conjecture_B_high_H_core.py`](../conjecture_B_high_H_core.py).

**Headline.** On the `n≤9` corpus the hard core *is* closable — the **per-vertex bound**
`Cb_pv` gives `|C| ≤ Cb_pv ≤ R″` on **all 9014** graphs (max ratio 0.468), and three
weighted-Cauchy–Schwarz bounds also close it. **But every one of these fails at scale.**
On the adversarial **deg2+dense** family the weighted-CS bounds blow up immediately
(ratios 1.25–6.6 at `n≈40`), and the per-vertex bound — the lone survivor through
`n≈70` — **creeps past 1 at `n ≥ 100`** (1.006 at n=100, 1.023 at n=140). The actual
`|C|/R″` itself grows toward 1 on this family (0.52 → 0.84 as `n`: 30 → 140), so **B2′ is
asymptotically tightening there**: no bound with slack can close the dense-irregular
regime. This is the same `n≤9`-artifact trap that has recurred throughout; the hard core
is genuinely hard and asymptotic.

---

## TASK 1 — anatomy of `C` on the hard core (811 graphs, `n≤9`)

`H ∈ [0.286, 0.491]` (median 0.44). The negative `C` is driven by:
- **edges touching a minimum-degree vertex:** the top-20% edges by `|contribution|` carry
  a **median 0.59** of `|C|` on edges incident to a min-degree vertex;
- **hub-flat / leaf-large pattern:** on dominant edges `|f_h| < |f_l|` **87%** of the time
  (Fiedler small at the high-degree endpoint, large at the low-degree one);
- **degree gaps** `d_h−d_l` on dominant edges: median 3, max 6;
- the product `f_h(f_h−f_l) < 0` on **64%** of dominant edges — this is what makes the
  oriented sum negative.

So `C<0` comes from low-degree vertices carrying large Fiedler mass adjacent to flat hubs
across a big degree gap — exactly the deg2+dense morphology.

## TASK 2/3 — bounds on `|C|`, and where they hold

`bound/R″` (want `≤ 1`); all are valid upper bounds on `|C|` unless noted:

| bound | hard core (811, n≤9) | full corpus (9014, n≤9) | **deg2/3+dense at scale** |
|---|---|---|---|
| (orig) `Cb_cs` | max 2.00, covers 0% | max 2.35, 90.2% | fails |
| (a) hub-flat | max 10.9, 0% | max 25.7, 0.1% | fails |
| (b) `½E_disc` (not always valid) | max 2.20, 18% | max 2.64, 83% | fails |
| (c) `w=d_l−1` | max 0.85, **100%** | max 0.92, **100%** | **1.25 → fails** |
| (c) `w=1/(d_h−λ)²` | max 0.91, **100%** | max 0.99, **100%** | **3.97 → fails** |
| (c) `w=Δd` | max 0.96, **100%** | max 1.04, 99.99% | **6.59 → fails** |
| **(d) per-vertex** | max **0.26**, **100%** | max **0.47**, **100%** | **0.81 (n≤70) → 1.02 (n≥100) fails** |

- The **weighted-CS bounds (c)** close the entire `n≤9` corpus but are pure small-`n`
  artifacts: on deg2+dense (`n≈40`) they immediately exceed 1.
- The **per-vertex bound (d)** `Cb_pv = Σ_h |f_h| · |g_h|`, `g_h = Σ_{l∈N(h), d_l<d_h}
  (d_h−d_l)(f_h−f_l)` (group `C = Σ_h f_h g_h` by high endpoint, triangle-inequality), is
  far the strongest: max 0.47 on the corpus, and it survives moderate hard families
  (deg2+dense 0.81, deg3 0.55, WS 0.09, ER 0.18 — **207/207** at `n` up to 60).

## The scale test — per-vertex bound on deg2+dense vs `n`

| `n` | max `Cb_pv/R″` | actual max `\|C\|/R″` |
|---|---|---|
| 30 | 0.711 | 0.523 |
| 50 | 0.988 | 0.632 |
| 70 | 0.966 | 0.703 |
| 100 | **1.006** | 0.765 |
| 140 | **1.023** | 0.836 |

The per-vertex bound **crosses 1 at `n ≈ 100`** — it fails on the same lock-breaker family
that has defeated every prior bound, just at larger `n`. Meanwhile the *true* `|C|/R″`
grows 0.52 → 0.84: **B2′ is getting tight on deg2+dense as `n → ∞`** (consistent with the
earlier finding that this family drives `λ₂(T)/λ₂(G)` toward its extreme). A bound with
any fixed slack must eventually fail. (Pendant — degree-1 — variants are benign: the
degree-1 vertex is never a high endpoint, so `Cb_pv = 0`.)

## TASK 4 — combining

`min` over all valid bounds closes the `n≤9` corpus (max 0.26) but inherits the
per-vertex failure at scale. A convex combination `α·Cb_cs + (1−α)·Cb_hub` does **not**
help (both endpoints exceed 1 on some graph; min over `α` is `> 1`). No combination of
these bounds closes B2′ uniformly in `n`.

---

## Synthesis

- The high-`H` hard core is **closed on `n≤9`** by the per-vertex bound (margin 2×) and
  by weighted-CS — but this is the **small-`n` mirage** the project has hit before.
- **At scale, all bounds fail** on deg2+dense; the per-vertex bound (the best) crosses 1
  at `n ≈ 100`. The reason is structural: `|C|/R″ → ~1` on deg2+dense, so **B2′ is
  asymptotically tight there** and no slack-bound can close it.
- **Anatomy is clear and consistent:** `C<0` is produced by min-degree vertices with
  large Fiedler mass next to flat hubs across large degree gaps. The hub-flatness lemma
  (`f_h² ≤ d_h/(d_h−λ₂)²`, formalized in `Paper14.lean`) controls `f_h`, but `f_l` at the
  low-degree endpoint is *not* small, and that is what the bounds cannot tame at scale.

**Conclusion for the proof.** Closing B2′ requires an argument that is **exact on the
deg2+dense asymptote** (where `|C|/R″ → 1`), not a slack bound. The per-vertex grouping
`C = Σ_h f_h g_h` is the right structural handle (tightest by far, `0.47` on corpus), but
making `Σ_h f_h g_h ≥ −R″` rigorous needs the eigenvector equation at the low-degree
endpoints — the same `λ₂`-minimality coupling identified in every prior round, now pinned
to the deg2+dense extremal family.

### Caveats
`λ₂`, `f` numerical. Hard-core anatomy and bound table over the 9020-graph `n≤9` corpus;
scale test over 207 hard-family graphs (`n≤60`) plus a deg2+dense sweep to `n=140`. All
bounds are exact upper bounds on `|C|` (verified `|C| ≤ B`); the failures are `B ≤ R″`
breaking at scale. B2′ itself holds throughout (max actual `|C|/R″ = 0.84` at `n=140`);
it is the *bounds*, not B2′, that fail.
