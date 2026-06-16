# Conjecture B — complement of the hard cases, and a discovery: the "lock" is false at scale

Goal: characterize the complement `H = K_n − G` of the tight small-A graphs
(`W/R'' > 0.7`). The search did that **and** uncovered a constructed family that
drives `W/R''` past 1 — which, on careful checking, is **not** a counterexample to
Conjecture B but a **refutation of the min-degree "lock" `W ≤ R''` itself** as a
universal sufficient condition. Code:
[`conjecture_B_complement_hard_cases.py`](../conjecture_B_complement_hard_cases.py).

**Two headline findings:**
1. The tight complements are **generic dense graphs with one dominant vertex**
   (= one low-degree `G`-vertex) and a *localized* Fiedler vector — **not** stars,
   splits, thresholds, or unions of stars (those structured families top out at
   `W/R'' ≈ 0.68`).
2. **The lock `W ≤ R''` is FALSE at scale.** A constructed family ("one degree-2
   vertex + dense `G(n−1,q)` background") gives `W/R'' → 1.4+`, growing with `n`,
   while **Conjecture B holds with margin `Q ≈ 2.2`**. The casualty is the
   min-degree relaxation, not B.

---

## Part 1 — the tight complements (the original task)

Over 12 721 small-A graphs searched, **51 had `W/R'' > 0.7`; global max `W/R'' =
0.915`** (the random search never reached 1). Their complements `H`:

- **all classified "generic"** — none is a star / union-of-stars / split / threshold;
- degree sequence of `H` always has **one dominant vertex** (e.g. `[13,9,8,7,7,…]`
  for `n=16`): one vertex missing almost all edges = **one low-degree `G`-vertex**
  (`δ(G) = 2–3`), atop a dense, irregular background;
- the top Laplacian eigenvector `f` of `H` is **localized** (participation ratio
  `≈ 1.2–1.6`, i.e. effectively supported on 1–2 vertices), concentrated near the
  dominant vertex;
- `λ₂(G)` is **simple** (mult 1) on the tight cases — so `W` is well-defined.

The **structured families undershoot**: scanning double-stars, `K_a`+pendants,
threshold graphs, and split graphs (as complements) reached only `W/R'' ≈ 0.68`
(threshold), `0.58` (double-star), `0.57` (clique+pendants). **The extremal
complement is not a named family** — it is "dominant vertex + dense irregular
background."

---

## Part 2 — the discovery: `W/R''` exceeds 1

Constructing the suggested extremal directly — **vertex 0 of degree `d₀=2`, plus a
dense `G(n−1, q)` background, `q ≈ 0.6–0.7`** — and scanning `n`:

| n | max `W/R''` |
|---|---|
| 14 | 0.90 |
| 18 | 1.05 |
| 22 | 1.24 |
| 26 | 1.30 |
| 28 | 1.42 |

`W/R''` **crosses 1 around `n ≈ 18` and keeps growing** — the lock fails by an
unbounded margin in `n` on this family.

---

## Part 3 — it is NOT a counterexample to B; the lock is the casualty

Checking the violating graphs directly (each: `A < 3/2`, `λ₂(G)` simple,
`T(G)` connected):

| n | W/R'' | λ₂(G) | λ₂(T(G)) | **B holds?** | Q=λ₂(G)/λ₂(T) |
|---|---|---|---|---|---|
| 20 | 1.11 | 1.908 | 0.847 | ✅ | 2.25 |
| 28 | 1.27 | 1.948 | 0.905 | ✅ | 2.15 |
| 28 | 1.37 | 1.970 | 0.939 | ✅ | 2.10 |
| 29 | 1.16 | 1.927 | 0.842 | ✅ | 2.29 |

**Conjecture B holds with a wide margin (`Q ≈ 2.1–2.3`) on every one.** So `W > R''`
is *not* a violation of B. Over 400 such constructed graphs (n=20–29):

```
  f^T L_t f  >  R''   (the LOCK fails)                       : 100%
  f^T L_t f  ≤  λ₂(fᵀQf − S²/m)  (the TRUE lift bound holds) : 100%
  Conjecture B (λ₂(T) ≤ λ₂(G))                                : 100%
```

**Root cause.** The lock `W ≤ R''` comes from the relaxation
`t_ab ≤ min(d_a,d_b) − 1` (min-degree weights `L_md ⪰ L_t` entrywise). The lock is
equivalent to `fᵀL_md f ≤ λ₂(fᵀQf − S²/m)`. On these graphs the **min-degree
weights overshoot the true triangle counts enough that `fᵀL_md f` (and even
`fᵀL_t f`) exceed `R''`** — but the *correct* lift RHS is `λ₂(fᵀQf − S²/m) =
λ₂(2fᵀDf − λ₂ − S²/m)`, which is **larger** than `R''` (the v3+ "R''" form
`λ₂(fᵀDf − λ₂ + 1 − S²/m)` is smaller by `λ₂(fᵀDf − 1)`), and the true triangle
form stays under it. The lift Rayleigh quotient
`R_T = fᵀL_t f /(fᵀQf − S²/m)` satisfies `λ₂(T) ≤ R_T ≤ λ₂(G)` throughout — the
**original lift route survives**.

---

## Part 4 — implications (a correction to the recent direction)

- **The min-degree "lock `W ≤ R''`" is not a universally valid sufficient
  condition for B.** It holds on the small/random corpora tested earlier but
  **fails by an unbounded margin** on the constructed "low-degree vertex + dense
  background" family (n ≳ 18). So the recent line built on it — `(C4)`, the
  large-A/small-A regime split, the "irreducible small-A lock," and the complement
  reformulation of `W ≤ R''` — analyzes a condition that is **too strong** (false
  at scale). Those analyses remain correct *as analyses of `W ≤ R''`*, but that
  target cannot prove B.
- **The valid object is the original lift bound with *actual triangle counts*:**
  `λ₂(T(G)) ≤ R_T = fᵀL_t f /(fᵀQf − S²/m)`, and B ⟸ `R_T ≤ λ₂(G)`, i.e.
  `fᵀL_t f ≤ λ₂(fᵀQf − S²/m)`. This survives on the family that breaks the lock
  (100%). The min-degree relaxation `t_ab ≤ min(d_a,d_b)−1` must be **abandoned** —
  it is the lossy step.
- **The canonical extremal family** (for the lock's failure, and for the tight
  `W/R''`) is **`G =` {one degree-`O(1)` vertex} ∪ {dense `G(n−1,q)` background}**,
  `q ≈ 0.6–0.7`. Its complement `H` = {one dominant vertex} + {sparse-ish
  background}; `λ₂(G) ≈ const`, `λ₂(T) ≈ const < λ₂(G)`, so B holds with `Q ≈ 2.2`,
  while the min-degree weights make `W` grow and overshoot `R''`.

### Caveats
- `λ₂`, `f` numerical; violating graphs have simple `λ₂` (mult 1), `T(G)` connected,
  `A < 3/2` — genuine small-A, not artifacts. B verified by direct
  `λ₂(T) ≤ λ₂(G)` computation. The lift-RHS comparison
  `fᵀL_t f ≤ λ₂(fᵀQf − S²/m)` is checked to hold 100% on the same family.
- This supersedes the optimism of `conjecture_B_small_A*.md` /
  `conjecture_B_regime_split.md`: those characterize `W ≤ R''`, which this shows is
  not the right (true) target. The lift bound `R_T ≤ λ₂(G)` is.
