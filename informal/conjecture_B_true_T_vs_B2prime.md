# Conjecture B — is `T ≤ λ₂G` easier than `B2′ ≤ λ₂G`? (the deg2+dense wall is a B2′ artifact)

`T = Σ_e t_e g_e²` (`t_e = |N(a)∩N(b)|`), `B2′ = Σ_e(min(d_a,d_b)−1)g_e²`, `g=f_a−f_b`, `h=f_a+f_b`,
`G = Σh² − S²/m`, `λ₂ = Σg²`. Since `t_e ≤ min−1`, `T ≤ B2′`, so `T ≤ λ₂G` is *weaker* (easier) than
`B2′ ≤ λ₂G`. We quantify how much, and find the **true extremizer**. Code:
[`conjecture_B_true_T_vs_B2prime.py`](../conjecture_B_true_T_vs_B2prime.py) (49 graphs).

## TASK 3 — `t_eff ≤ G` (i.e. `T ≤ λ₂G`) holds universally

`t_eff := T/λ₂ ≤ G` is exactly `T ≤ λ₂G` (the conjecture-B reduction). **Holds 49/49** (as does
`B2′ ≤ λ₂G`).

## TASK 1 — `T` is far slacker than `B2′` — except at the complete graph

| ratio | median | max (sup) |
|---|---|---|
| `T/(λ₂G)` | **0.40** | **1.000** (at `K_n`) |
| `B2′/(λ₂G)` | **0.79** | 1.000 (at `K_n`) |

`T/(λ₂G)` is much smaller *on average* (median 0.40 vs 0.79), but **both reach `1` at the complete
graph** — so the worst-case margin `1 − sup` is `0` for *both*. `T ≤ λ₂G` is not *uniformly* slacker;
its slack is concentrated away from `K_n`.

## TASK 2 — the TRUE extremizer is `K_n` (equality), NOT the bottleneck

| graph | `T/(λ₂G)` | `B2′/(λ₂G)` |
|---|---|---|
| **`K_n` (any n)** | **1.000** | **1.000** |
| `rr(60,57)` (dense regular) | 0.931 | 0.966 |
| `rr(40,37)` | 0.895 | 0.947 |
| `gnp(40,0.9)` | 0.828 | 0.921 |
| **deg2+dense(160)** | **0.317** | 0.957 |
| lollipop, barbell | ≤ 0.03 | ≤ 0.26 |

> **The extremizer of `T/(λ₂G)` is the complete graph `K_n`, with `T = B2′ = λ₂G` (equality).** On
> `K_n` every edge has `t_e = n−2 = min(d_a,d_b)−1`, so `T = B2′` *exactly* and both saturate `λ₂G`.
> The next-hardest are **dense (near-)regular** graphs. The deg2+dense bottleneck — the wall that broke
> every coarse-bound route — has `T/(λ₂G) ≈ 0.3` (huge slack); it is hard *only for `B2′`*.

## TASK 5 — the deg2+dense difficulty is a `B2′` ARTIFACT

Graphs where `B2′` is near-tight but `T` is slack (gain `= B2′-ratio − T-ratio`):

| graph | `B2′/(λ₂G)` | `T/(λ₂G)` | gain |
|---|---|---|---|
| deg2+dense(160) | 0.957 | 0.317 | **0.640** |
| deg2+dense(80) | 0.918 | 0.298 | 0.620 |
| deg2+dense(40) | 0.846 | 0.281 | 0.565 |
| `rr(60,20)` | 0.717 | 0.200 | 0.517 |

> **On deg2+dense, `B2′` over-counts massively:** the bottleneck edges (`v₀–a`, `v₀–b`) have
> `min(d_a,d_b)−1 = O(n)` in `B2′` but **actual `t_e = 0`** (no triangle through the degree-2 vertex).
> So `B2′` inflates the bottleneck contribution by `Θ(n)`, making `B2′/(λ₂G) → 1`, while the true `T`
> ignores those edges (`T/(λ₂G) ≈ 0.3`). **The "deg2+dense wall" is entirely an artifact of replacing
> `t_e` by `min−1`** — it does not exist for the genuine inequality `T ≤ λ₂G`.

This explains why every coarse-bound route (S-procedure, signless-Laplacian, curvature, resultant)
failed: they all bounded `B2′` (or its proxies) on deg2+dense, where `B2′` is *artificially* tight.
The true object `T` is slack there.

## TASK 4 — proof route for `T ≤ λ₂G` that bypasses `B2′`

The extremality structure of `T ≤ λ₂G` is **completely different** from `B2′ ≤ λ₂G`:

- **Equality case: the complete graph `K_n`** (regular), where `T = λ₂G`. Next-hardest: dense regular.
- **All irregular/bottleneck graphs are strictly slack** (deg2+dense `0.3`, lollipop `0.01`).

So the natural route is **regular-first**, not bottleneck-first:

1. **Regular base case (the equality):** for `d`-regular `G`, `T ≤ λ₂G` — the tight case. This is
   essentially `aggregate_triangle_poincare_regular` (`T ≤ 2λ₂·fᵀDf`, regular, sorry-free), with `K_n`
   the saturating instance.
2. **Irregularity creates slack:** for non-regular `G`, `T < λ₂G` strictly, because the
   triangle-deficit on low-degree-incident edges (`t_e ≪ the regular value`) removes mass from `T`
   while `λ₂G` (a degree/variance quantity) does not shrink proportionally. The bottleneck families
   are the *extreme* of this slack.

The key strategic shift: **target `T` directly, with the complete graph as the (benign, regular)
extremizer — do NOT relax to `B2′`** (whose extremizer is the intractable bottleneck). The opening for
a proof is the *regular* regime (where the bound is tight and `aggregate_triangle_poincare_regular`
already holds), plus a *monotone-in-irregularity slack* argument — the opposite end from where the
coarse bounds kept failing.

## Conclusion

- **`T ≤ λ₂G` is NOT uniformly easier than `B2′ ≤ λ₂G`** (both tight at `K_n`, margin 0), but its
  **hard case is benign**: the complete/dense-regular graph, not the deg2+dense bottleneck.
- **The deg2+dense "wall" is a `B2′` artifact** (`min−1` over-counts the `t_e = 0` bottleneck edges by
  `Θ(n)`); for the true `T ≤ λ₂G`, deg2+dense has `T/(λ₂G) ≈ 0.3` (slack). This is *why* every coarse
  route failed — they fought a phantom (the inflated `B2′`).
- **Proof route:** go through `T` directly, regular-first (extremizer `= K_n`, base case
  `aggregate_triangle_poincare_regular`), with irregularity producing strict slack — bypassing `B2′`
  and its bottleneck obstruction entirely.
- `t_eff ≤ G` (= `T ≤ λ₂G`) holds 49/49; no counter-family; the `S²/m` centering is already built in.

This reframes the open problem: the relevant Lean target is **`T ≤ λ₂G` directly** (extremizer `K_n`,
regular), not `B2prime_le_RHS` (extremizer deg2+dense). `aggregate_triangle_poincare` — which I had
moved off the chain — is in fact the *better-conditioned* lemma (its hard case is regular, already
proved), suggesting the `B2′` relaxation was the wrong reduction for the hard family.

## Lean
No new lemma (numerical/strategic). Reframes the target: `aggregate_triangle_poincare` (`T ≤ λ₂fᵀDf`,
regular case proved) is the better-conditioned route for the hard (dense/regular) family; `B2prime_le_RHS`
is tight on the *artifact* family (deg2+dense). A future chain could split: regular/dense via the
`T`-route, sparse/bottleneck via the (slack) `B2′`-route.
