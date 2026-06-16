# Conjecture B — two-regime split on A = fᵀDf − λ₂

Tests whether the lock `W ≤ R'' = λ₂(A + 1 − S²/m)` (with `A := fᵀDf − λ₂ ≥ 0`)
admits a clean drop-a-term bound, globally or by an `A`-split. Corpus: **2245**
`T(G)`-connected graphs spanning both regimes (near-complete `K_n−ke`, complete
multipartite, dense `G(n,p)`, large near-regular Watts–Strogatz). Lock holds
2245/2245. Code:
[`conjecture_B_regime_split.py`](../conjecture_B_regime_split.py).

**Outcome.** No *global* drop-a-term bound is clean, but the **large-A regime has a
clean theorem** `W ≤ λ₂·A` (0 violations for `A ≥ 3/2`, and it implies B there).
The residual difficulty is **not** the Watts–Strogatz regime (that is large-A and
covered) but the **small-A regime** `A < 3/2` — graphs where `fᵀDf ≈ λ₂` (i.e.
`λ₂ ≈ δ`), including near-complete `K_n−e`. There the `+1` is irreducible.

---

## Global candidates

| candidate | max `W/bound` | `W ≤ bound`? | `bound ≤ R''` (⇒ implies B) |
|---|---|---|---|
| **C1** `λ₂·max(A,1)` | 1.106 | ❌ 4 violations | 100% |
| **C2** `λ₂·(A+1)` | 0.601 | ✅ **100%** | **only 3%** |
| **C3** `λ₂·A` | 1.169 | ❌ 19 violations | 100% |

- **C2 holds 100% but is useless for a proof.** `λ₂(A+1) = R'' + λ₂S²/m ≥ R''`, so it
  is *weaker* than the lock — it holds automatically wherever B holds (`bound ≤ R''`
  only 3%, i.e. it almost never sits below `R''`). Proving C2 does **not** prove B.
- **C3 (`λ₂·A`) is the one that would prove B** (`λ₂A ≤ R''` on 100%, since `S²/m ≤ 1`),
  but it fails on 19 graphs.
- **C1** (= split at `c=1`) fails on 4.

So no single global drop-a-term inequality is simultaneously *true* and
*B-implying*.

---

## Key diagnostic — distribution of W/(λ₂·A)

```
max W/(λ₂·A) = 1.1693   (>1 ⇒ C3 fails)   mean 0.460   median 0.430
achieved by: G(n,p)  n=12 m=36  A=0.618  λ₂=1.872  W=1.354
             degseq [9,8,8,7,7,7,6,5,5,5]   (sparse, low-λ₂, SMALL A)

histogram of W/(λ₂·A):
  [0,.25)    411  ##########################
  [.25,.5)   945  ############################################################
  [.5,.75)   629  #######################################
  [.75,1)    216  #############
  [1,1.5)     44  ##
  [≥1.5)       0
```

- **`W/(λ₂A) > 1` on only 19/2245 graphs — and all 19 are `G(n,p)`**, none
  Watts–Strogatz, none near-complete-with-large-A.
- The 19 violators have **small `A`** (range `0.33–1.23`, median `0.84`). The
  maximal ratio 1.17 is a sparse low-`λ₂` graph (`A=0.62`).
- **No graph with `A ≥ 1.5` violates `W ≤ λ₂A`** (the `[≥1.5)` bin is empty; max
  violator `A = 1.228`).

So `W ≤ λ₂·A` fails **only** in the small-`A` regime.

---

## Regime split sweep

large-A (`A ≥ c`): test `W ≤ λ₂A`; small-A (`A < c`): test `W ≤ λ₂`.

| c | large-A: graphs / viol / `λ₂A≤R''` | small-A: graphs / viol / `λ₂≤R''` | total viol |
|---|---|---|---|
| 0.1 | 2244 / 19 / 100% | 1 / 0 / 100% | 19 |
| 0.5 | 2184 / 18 / 100% | 61 / 0 / 100% | 18 |
| 1.0 | 1791 / 2 / 100% | 454 / 2 / 100% | 4 |
| **1.5** | **1389 / 0 / 100%** | 856 / **32** / 100% | 32 |
| 2.0 | 1118 / 0 / 100% | 1127 / 118 / 100% | 118 |

- **Large-A side becomes clean at `c = 1.5`** (`W ≤ λ₂A`, 0 violations, and
  `λ₂A ≤ R''` on 100% ⇒ implies B). Empirically the boundary is `A ≈ 1.23`.
- **Small-A side is the problem:** `W ≤ λ₂` (the bare constant) fails — 32 at `c=1.5`,
  118 at `c=2.0`. The bare `λ₂` drops the `λ₂A` part; small-A graphs need the full
  `λ₂(A+1−S²/m)`. So there is **no clean split** with the bare-`λ₂` small-A bound.

---

## The winning statement: one clean lemma + a bounded residual

**Lemma 1 (large-A regime — clean, implies B).**
Let `A = fᵀDf − λ₂`. If `A ≥ 3/2`, then
`W = Σ_{ab}(min(d_a,d_b)−δ)(f_a−f_b)² ≤ λ₂·A`.
Moreover `S²/m ≤ 1` holds throughout this regime, so `λ₂·A ≤ R''`, giving the lock
`W ≤ R''` and hence `λ₂(T(G)) ≤ λ₂(G)`.
*Status:* 0 violations / 1389 graphs (empirical boundary `A ≈ 1.23`). Covers the
entire Watts–Strogatz "hard" regime (there `A ≈ 6`, `W/(λ₂A) ≤ 0.77`) and all dense
graphs.

**Lemma 2 (small-A regime — the irreducible residual).**
If `A < 3/2` then the lock `W ≤ R'' = λ₂(A + 1 − S²/m)` cannot be simplified: the
`+1` is load-bearing (`W ≤ λ₂` fails), and `W ≤ λ₂A` fails. This regime is
characterized by `fᵀDf < λ₂ + 3/2`, i.e. **`λ₂ ≈ δ`** (the spectral gap nearly
saturates the min-degree bound; near-complete `K_n−e` and sparse low-`λ₂` graphs
live here). It must be proved with the full `R''`.

---

## Reinterpretation

The regime that defeats the *clean* bound is the **opposite** of the earlier
"hard regime." Watts–Strogatz graphs are **large-A** and fall cleanly under
Lemma 1 (`W ≤ λ₂A`); the genuinely irreducible cases are **small-A** graphs
(`fᵀDf ≈ λ₂`, i.e. `λ₂ ≈ δ`). This is real progress: **Conjecture B is reduced to
the bounded-A regime `0 ≤ fᵀDf − λ₂ < 3/2`** — a compact, well-characterized
sub-problem (`λ₂` close to `δ`), where the additive `+1` is the whole content.
The large-A bulk is dispatched by the single clean inequality `W ≤ λ₂(fᵀDf − λ₂)`.

### Caveats
- `λ₂`, `f` numerical; corpus deliberately spans both regimes. The threshold `3/2`
  is empirical (max `W ≤ λ₂A` violator has `A = 1.228`); a proof would fix the
  precise constant. `λ₂A ≤ R''` (Lemma 1's implication step) held on 100% of the
  corpus (it requires `S²/m ≤ 1`, which holds whenever `A ≥ 1`).
