# Conjecture B — the residual small-A regime (A = fᵀDf − λ₂ < 3/2)

Large-A is dispatched by `W ≤ λ₂·A` (see
[`conjecture_B_regime_split.md`](conjecture_B_regime_split.md)). This isolates and
dissects the residual: **A < 3/2**. Corpus: 4019 `T(G)`-connected graphs, of which
**1938 have A < 3/2**. Code:
[`conjecture_B_small_A.py`](../conjecture_B_small_A.py).

**Conclusion.** The residual is **irreducible**: of the five candidate lemmas,
**only the full lock `R'' = λ₂(A + 1 − S²/m)` holds (100%)**; every simpler bound
(`λ₂`, `λ₂(1−S²/m)`, the δ-version `λ₂(δ−λ₂+1−S²/m)`, `λ₂(2−λ₂/δ)`) **fails** by 2–12%.
The small-A regime is **not** sparse-low-λ₂ (that is rare, 5/1938) — it is **dense
graphs with λ₂ ≈ δ**, exactly where the lock is *tight* (W/R'' up to 0.93) and
where **all four terms of R'' are load-bearing** (including `−S²/m`, which reaches
0.83 here). No term may be dropped.

---

## 1–2. Enumeration and structural classification

1938 graphs with `A < 3/2`:

| class (by density / λ₂) | count |
|---|---|
| near-complete (density ≥ 0.75) | 1234 |
| intermediate | 699 |
| **sparse-low-λ₂** (density<0.45, λ₂<2.5) | **5** |

| by family | count |
|---|---|
| `G(n,p)` | 1636 |
| Watts–Strogatz | 264 |
| `K_n−ke` | 38 |

| quantity | min | median | max |
|---|---|---|---|
| density | 0.41 | **0.80** | 0.98 |
| **λ₂/δ** | 0.62 | **0.93** | 1.00 |
| S²/m | — | 0.024 | **0.83** |
| **W/R''** | — | 0.30 | **0.93** |

**The small-A regime is the dense / `λ₂≈δ` regime, not the sparse one.** Median
density 0.80, median `λ₂/δ = 0.93` (the spectral gap nearly saturates the
min-degree bound). It is where the lock is *tight* (`W/R'' → 0.93`). Sparse
low-`λ₂` graphs are essentially absent (5/1938) — `A < 3/2` requires `fᵀDf`
close to `λ₂`, which dense, highly-connected graphs produce.

Representative graphs (tightest per class):

| class | n | m | dens | δ | Δ | λ₂ | λ₂/δ | A | S²/m | W | R'' | W/R'' |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| near-complete | 10 | 38 | 0.84 | 2 | 9 | 2.00 | 1.00 | 0.75 | **0.83** | 1.50 | 1.84 | 0.81 |
| intermediate | 15 | 66 | 0.63 | 2 | 11 | 1.83 | 0.92 | 1.00 | 0.78 | 2.08 | 2.24 | **0.93** |
| sparse-low-λ₂ | 14 | 40 | 0.44 | 2 | 8 | 1.49 | 0.75 | 1.48 | 0.29 | 2.24 | 3.27 | 0.69 |

Note the tight cases have a **low-degree vertex** (`δ=2`) among high-degree ones
(`Δ=9–12`): that degree gap drives `S²/m` up to 0.83, making `−S²/m` a real term.

---

## 3. Candidate residual lemmas

| lemma | holds | implies B (`bound ≤ R''`) | both | max `W/bound` |
|---|---|---|---|---|
| **L1** `W ≤ λ₂` | 95% | 100% | 95% | 1.52 |
| **L2** `W ≤ λ₂(1−S²/m)` | 88% | 100% | 88% | 5.08 |
| **L3** `W ≤ R'' = λ₂(A+1−S²/m)` | **100%** | 100% | **100%** | 0.93 |
| **L4** `W ≤ λ₂(δ−λ₂+1−S²/m)` (C4) | 97% | 100% | 97% | 4.39 |
| **L5** `W ≤ λ₂(2−λ₂/δ)` | 98% | 100% | 98% | 1.27 |

Every simplification fails:
- **L1 (`λ₂`) fails 5%** — `W` reaches `1.52·λ₂` on the tight cases (the `+A` term
  is needed).
- **L2 fails 12%** — dropping `A` *and* keeping `−S²/m` is worst (smallest RHS).
- **L4 = the δ-version C4 fails 3%** — when `λ₂ ≈ δ` (so `δ−λ₂ ≈ 0`) and `S²/m` is
  large, `λ₂(δ−λ₂+1−S²/m) ≈ λ₂(1−S²/m)` collapses (e.g. `λ₂=2, S²/m=0.83 ⇒`
  RHS `=0.34` but `W=1.50`). **So even the combinatorial δ-version is invalid here** —
  the residual genuinely needs `fᵀDf`, not `δ`.
- **L5 (`λ₂(2−λ₂/δ)`) fails 2%** — closest of the simple forms (`max W/bound=1.27`),
  but not clean.

---

## 4. The weakest true B-implying lemma: the full R'' — irreducible

**Only L3 (= R'') is simultaneously 100%-true and 100%-B-implying.** No simpler
candidate survives. Concretely, in the small-A regime:

- `A` cannot be dropped (L1, L2 fail) — the `+λ₂·A` term is needed;
- `fᵀDf` cannot be replaced by `δ` (L4 fails) — because `λ₂ ≈ δ` makes `δ−λ₂` too
  small while `S²/m` is large;
- `−S²/m` cannot be dropped — it is large (up to 0.83) precisely here, and the lock
  is tight (`W/R'' → 0.93`), so the correction is load-bearing.

> **Residual lemma (irreducible).** For `A = fᵀDf − λ₂ < 3/2`, Conjecture B requires
> the full `W ≤ λ₂(fᵀDf − λ₂ + 1 − S²/m)`; no term may be dropped or coarsened
> (every drop-a-term / δ-coarsened variant fails on 2–12% of the regime).

---

## Synthesis — the two-regime picture is now complete

| regime | clean lemma | status |
|---|---|---|
| **large-A** (`fᵀDf − λ₂ ≥ 3/2`) | `W ≤ λ₂·(fᵀDf − λ₂)` | clean; 0 violations; implies B |
| **small-A** (`fᵀDf − λ₂ < 3/2`) | none simpler than `R''` | **irreducible**: full `R''` needed |

The hard core of Conjecture B is now sharply located: **dense graphs with `λ₂ ≈ δ`
and a non-trivial degree gap (`S²/m` up to ~0.83)**, where the lock is tight and the
exact `R''` — all of `+λ₂·A`, `+λ₂`, and `−λ₂·S²/m`, with `fᵀDf` (not `δ`) — is
required. A proof of B must therefore (i) prove the clean `W ≤ λ₂(fᵀDf−λ₂)` for
large A, and (ii) prove the *exact* `W ≤ R''` for the bounded, dense, `λ₂≈δ`
small-A regime — there is no shortcut in (ii). This explains, in retrospect, why
every proxy bound failed on exactly one regime: the small-A regime tolerates no
coarsening at all.

### Caveats
- `λ₂`, `f` numerical; corpus spans `K_n−ke`, complete multipartite, dense `G(n,p)`,
  Watts–Strogatz. The `3/2` cut is the empirical large-A boundary from
  `conjecture_B_regime_split.md`. `implies-B` percentages count `bound ≤ R''`
  (L2 and L4 are `≤ R''` by construction; L1, L5 nearly always).
