# Conjecture B — decomposing the exact lock on the hard regime

Studies **only** the hard regime: 50 large, near-regular, low-μ₂, high-ΣH
Watts–Strogatz-type graphs (`n=20–41`, `Δ/δ≤2`, `α=W/(μ₂fᵀDf)∈[1.75,4.66]` — all
proxy bounds fail here). No new bounds; just decompose `W ≤ R''`,
`R'' = λ₂·fᵀDf − λ₂² + λ₂ − λ₂·S²/m` (terms `T1,T2,T3,T4`). Code:
[`conjecture_B_hard_regime.py`](../conjecture_B_hard_regime.py).

**Headline.** The proxy-hard regime is **lock-easy**: `W/R'' ∈ [0.49, 0.60]` — the
lock holds with a **40–50% margin**. The slack comes from **`fᵀDf − λ₂` being
large** (`fᵀDf ≈ 14`, `λ₂ ≈ 8`): even the *stronger* bound `W ≤ λ₂(fᵀDf−λ₂)` holds
here (max ratio 0.77). The `+1` term — load-bearing on near-*complete* graphs — is
**not** load-bearing here, and the `−S²/m` correction is **negligible** (`S≈0`
because the graph is near-regular). So the two extreme regimes hold for *different*
reasons, which is exactly why no single proxy closes both.

---

## Term table (tightest 12 of the 50, by W/R'')

| n | m | λ₂ | μ₂ | fᵀDf | S | W | T1=λ₂fᵀDf | T2=−λ₂² | T3=+λ₂ | T4 | R'' | margin | W/R'' |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 37 | 296 | 8.01 | 0.54 | 14.67 | −1.10 | 36.82 | 117.5 | −64.2 | 8.01 | −0.03 | 61.3 | 24.5 | **0.600** |
| 35 | 280 | 8.44 | 0.57 | 13.66 | −1.96 | 31.01 | 115.3 | −71.3 | 8.44 | −0.12 | 52.4 | 21.4 | 0.592 |
| 37 | 296 | 7.93 | 0.53 | 14.36 | −2.50 | 34.21 | 113.8 | −62.8 | 7.93 | −0.17 | 58.7 | 24.5 | 0.583 |
| 33 | 264 | 9.77 | 0.67 | 14.01 | −2.04 | 29.21 | 136.9 | −95.5 | 9.77 | −0.16 | 51.0 | 21.8 | 0.572 |
| 25 | 150 | 5.43 | 0.53 | 9.38 | −2.60 | 15.09 | 51.0 | −29.5 | 5.43 | −0.25 | 26.6 | 11.5 | 0.567 |
| 35 | 315 | 9.93 | 0.60 | 15.57 | 0.59 | 35.88 | 154.6 | −98.7 | 9.93 | −0.01 | 65.9 | 30.0 | 0.545 |

(`W/R''` over all 50: min 0.494, max 0.600.)

---

## Q1 — where does the margin come from?

Mean term-as-fraction-of-`R''` over the 50 hard graphs:

| term | mean term/R'' | mean |term| |
|---|---|---|
| `T1 = λ₂·fᵀDf` | **+2.44** | 106.8 |
| `T2 = −λ₂²` | **−1.63** | 70.8 |
| `T3 = +λ₂` (the "+1") | +0.20 | 8.3 |
| `T4 = −λ₂·S²/m` | **−0.008** | 0.28 |

And `W` never reaches even the *first two* terms:

| test | exceed rate |
|---|---|
| `W > T1 (=λ₂fᵀDf)` | **0%** |
| `W > T1+T2 (=λ₂(fᵀDf−λ₂))` | **0%** |
| `W > T1+T2+T4` (drop the +1) | **0%** |

**Answer.** The margin is carried by the **`λ₂·fᵀDf` vs `−λ₂²` balance**: `T1` is
~2.4× `R''` and overwhelms the `−λ₂²` penalty, leaving `W` (≈0.55·R'') comfortably
below `T1+T2 = λ₂(fᵀDf−λ₂)` already. The `+1` term adds a further ~0.20·R'' of
slack but is **not needed** (W is below `T1+T2` without it). The `−S²/m` correction
is **negligible** (`mean S²/m = 0.036`, `|T4|/R'' ≈ 0.008`) — because near-regular
graphs have `S = Σd_v f_v ≈ d̄·Σf_v = 0`. **The slack is `fᵀDf − λ₂` being large.**

---

## Q2 — the tightest graph: what is load-bearing?

Tightest: `n=37, m=296, W=36.82, R''=61.31, W/R''=0.600, margin=24.5`.

- `margin (24.5) > T3=+λ₂ (8.0)` — removing the `+1` would leave margin `16.5 > 0`:
  the **`+1` is NOT load-bearing here** (and `margin < +λ₂` on **0%** of the 50).
- `margin < λ₂² = |T2|` on **100%** — the `−λ₂²` penalty is the dominant drag, but
  `T1 = λ₂·fᵀDf` (= 117.5) clears it (`117.5 − 64.2 = 53.3 > W = 36.8`).
- **What breaks first under perturbation:** the balance `λ₂·fᵀDf` vs `λ₂²`, i.e.
  the gap `fᵀDf − λ₂`. Pushing `λ₂` up toward `fᵀDf` (making the graph more
  expander-like relative to its degree) shrinks `T1+T2 = λ₂(fᵀDf−λ₂)` and is what
  would eventually threaten the lock — not the `+1` or the `S²/m` correction.

---

## Q3 — are the two ratios bounded by 1 here?

| ratio | max | mean | >1 ? |
|---|---|---|---|
| `W/(λ₂·fᵀDf)` | 0.313 | 0.223 | never |
| **`W/(λ₂·(fᵀDf−λ₂))`** | **0.771** | 0.651 | **never (0%)** |

Both are bounded by 1 on the hard regime. In particular **`W ≤ λ₂(fᵀDf−λ₂)` holds
on all 50** (the stronger, `+1`-free bound) — confirming the `+1` is dispensable
here. (`W/(λ₂fᵀDf) ≈ 0.22` shows `W` is only ~⅕ of the leading term.)

---

## Synthesis — why B holds on the hard regime, and the regime split

On large near-regular bottlenecked graphs the degree-weighted Fiedler norm
`fᵀDf ≈ d̄` is large while `λ₂` is moderate, so `fᵀDf − λ₂` is substantial and
`λ₂(fᵀDf − λ₂) ≈ 1.6×` the actual `W`. The lock is **not tight** here (`W/R'' ≤
0.6`); B holds with room, powered by the `λ₂·fᵀDf` term beating `−λ₂²`. The `+1`
and `−S²/m` terms are effectively inert (the latter because `S≈0`).

This pins down the **regime split** that has defeated every single proxy:

| regime | binding term | why the lock holds |
|---|---|---|
| near-**complete** (`K_n−e`, tight, `W/R''→1`) | the **`+1`** is load-bearing (`W ≈ λ₂(fᵀDf−λ₂)`) | the `+λ₂` slack |
| near-**regular WS** (this hard regime, `W/R''≈0.55`) | the **`fᵀDf−λ₂` gap** (`W ≤ 0.77·λ₂(fᵀDf−λ₂)`) | `λ₂·fᵀDf ≫ λ₂²` |

The two regimes are tight (or proxy-hard) for **opposite reasons**: near-complete
graphs lean on the additive `+1`; near-regular WS graphs lean on the multiplicative
`fᵀDf−λ₂` gap. A single clean proxy (`μ₂·fᵀDf`, `λ₂(fᵀDf−δ)`, etc.) captures one but
not the other — which is precisely why the proxy searches kept failing on exactly
one regime each. The exact `R''`, carrying **both** the `+1` and the full `fᵀDf`,
is what holds uniformly. A uniform proof must likewise retain both ingredients (and
can safely discard `−S²/m` in the near-regular regime, where `S≈0`).

### Caveats
- `λ₂`, `μ₂`, `f` numerical; hard regime = 50 large near-regular WS graphs with
  `α>1`, selected as the tightest by `W/R''`. The decomposition is exact (the four
  terms sum to `R''` by definition). `S≈0` is a near-regularity effect, not general.
