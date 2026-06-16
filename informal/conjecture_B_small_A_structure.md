# Conjecture B — structure of the small-A regime via the complement graph

The residual is `A = fᵀDf − λ₂ < 3/2`, where only the exact `W ≤ R''` survives
(see [`conjecture_B_small_A.md`](conjecture_B_small_A.md)). This document shows the
small-A lock is **exactly a statement about the complement (missing-edge) graph
`H = K_n − G`**, derives closed forms for the canonical families, and shows
small-A graphs are precisely the *perturbations of `K_n`*. Code:
[`conjecture_B_small_A_structure.py`](../conjecture_B_small_A_structure.py).

**Core result (the complement reformulation).** Every graph is `G = K_n − H`.
Since `L(G)+L(H)=nI−J`, on `1^⟂` we have `L(G)=nI−L(H)`, so (classical):

> `λ₂(G) = n − ν_max(H)`, and the **Fiedler vector of `G` = the top Laplacian
> eigenvector `f` of `H`** (eigenvalue `ν_max`).

Writing `deg_H`, `A_H`, `Δ_H` for the complement, this gives **exact** formulas
(verified to machine precision on the canonical families):

```
  d_v = (n−1) − deg_H(v),     δ = (n−1) − Δ_H,
  A   = fᵀDf − λ₂ = −fᵀA_H f − 1,
  S   = Σ d_v f_v = −Σ deg_H(v) f_v = −(deg_H · f),
  W   = Σ_{ab ∉ H} (Δ_H − max(deg_H a, deg_H b)) (f_a − f_b)²,
  R'' = (n − ν_max(H)) · (−fᵀA_H f − S²/m).
```

So **the small-A lock is entirely a low-rank statement about the small complement
`H`**, evaluated at its top eigenvector. (`λ₂ = n − ν_max(H)` verified to `2e-14`;
`A, S², W` match exactly when `λ₂` is simple — the residual `~0.7` in the random
check is `λ₂`-degeneracy, where `W` itself depends on the chosen Fiedler vector.)

---

## Canonical families — closed forms

| family (`H = …`) | λ₂ | A | W | W/R'' |
|---|---|---|---|---|
| `K_n − e` (`H` = 1 edge) | `n−2` | **0** | **0** | 0 |
| `K_n − M_k` (`H` = k-matching) | `n−2` | 0 | **0** | 0 |
| `K_n − △` (`H` = triangle) | `n−3` | 0 | **0** | 0 |
| **`K_n − star_k`** (`H = K_{1,k}`) | `n−k−1 (=δ)` | **(k−1)/(k+1)** | **(n−1−k)(k−1)/(k+1)** | `→ (k−1)/(2k)` |

All verified numerically (e.g. `n=20,k=3`: `A=0.500`, `W=8.000` exact; `n=40,k=15`:
`A=0.875`, `W=21.000` exact). Two structural facts emerge:

1. **`W = 0` whenever the complement `H` is regular on its support.** For `H` =
   edge / matching / triangle (all `r`-regular), the Fiedler vector `f` is supported
   on the missing-edge vertices, which all have degree `δ`, so `min(d_a,d_b)−δ = 0`
   on every edge carrying gradient. **`W > 0` requires an *irregular* complement**
   (uneven missing-degrees). The **star** (one vertex missing `k`, leaves missing
   `1`) is the minimal irregular case, and the only canonical family with `W>0`.
2. For the star, `λ₂ = δ` exactly (the `λ₂ ≈ δ` signature of small-A) and the lock
   ratio caps at `W/R'' → (k−1)/(2k) < 1/2` — **never tight**.

---

## Edit distance to `K_n` and missing-edge pattern

Over 600 small-A graphs, edit distance `|H| = C(n,2) − m`:

- missing-edge fraction `|H|/C(n,2)`: **min 0.01, median 0.19, max 0.51**.
- `corr(|H| fraction, W/R'') = +0.55` — **more missing edges ⇒ tighter lock**.
- the tight graphs (`W/R'' > 0.7`) have **dense complements** (`|H|` ≈ **45%** of
  all pairs), pattern "dense-H".

**So small-A is *not* synonymous with near-complete.** It spans from `|H|=1`
(`K_n−e`, `W=0`) up to `|H| ≈ 0.5·C(n,2)` (half-dense). The genuinely *tight* cases
have a **large, irregular complement** — graphs that are "roughly half-complete"
with an uneven missing-edge pattern — not the near-complete corner.

---

## Perturbation: `K_n` minus edges removed one at a time

Removing random edges from `K_n` (n=20, 30):

| #removed | λ₂ | fᵀDf | A | S²/m | W | R'' | W/R'' |
|---|---|---|---|---|---|---|---|
| 1 | n−2 | n−2 | 0.00 | 0.00 | 0.00 | n−2 | 0.00 |
| ~n/4 | ↓ | ↓ | ~0.5–1.0 | ~0.01 | small | ↑ | ~0.3 |
| ~n/2 | ↓ | ↓ | ~1.0–1.2 | ~0.01 | moderate | ↑ | ~0.3 |
| exits at ~10–16% removed | | | **≥3/2** | | | | ~0.3 |

- `A` grows roughly linearly with `#removed`, **exiting small-A (`A≥3/2`) at only
  ~10–16% of edges removed** — beyond that the graph is large-A, covered by
  `W ≤ λ₂(fᵀDf−λ₂)` (Lemma 1).
- Throughout random removal, **`W/R''` stays low (~0.16–0.35)** — `S²/m` stays tiny.
  Random perturbation never produces a tight lock; tightness needs a *structured*
  (dense, irregular) complement.

So the perturbation picture is clean: **near `K_n` the lock is slack** (`W=0` at
`H` = edge/matching/triangle; `W/R'' ≲ 0.35` for random small `H`), and the graph
leaves small-A into the Lemma-1 regime after ~10–16% edge removal. The hard tight
cases require a deliberately dense, irregular complement.

---

## Implication for a proof

The small-A regime collapses to a **perturbative statement about the complement's
top eigenpair**:

> **Small-A lock (complement form).** Let `f` be the unit top Laplacian eigenvector
> of `H` (eigenvalue `ν_max`), with `ν_max > n − 3/2` (the small-A condition,
> `−fᵀA_H f < 5/2`). Then Conjecture B is:
> `Σ_{ab∉H}(Δ_H − max(deg_H a, deg_H b))(f_a − f_b)² ≤ (n − ν_max)(−fᵀA_H f − (deg_H·f)²/m)`.

This is a genuine reduction:
- **Regular `H` ⇒ `W = 0`** (LHS vanishes): all of `K_n−e`, `K_n−matching`,
  `K_n−triangle`, cocktail-party — the lock is trivial. The content is *irregular*
  `H` only.
- The quantities are all low-rank in `H` (`f` supported on `H`'s non-isolated
  vertices), so for sparse `H` (near-complete `G`) it is a small finite computation;
  the closed forms above handle the star family exactly.
- A perturbation proof would expand around `H = ∅` (`K_n`, `W=0`) and bound the
  growth of the LHS vs RHS as edges are added to `H`, using that `f` is the top
  eigenvector of the small/structured `H`. The tight direction is dense irregular
  `H`, where `ν_max(H)` is large and `f` concentrates on `H`'s high-degree vertices.

### Caveats
- `λ₂ = n−ν_max(H)` is exact; `A,S,W` formulas are exact per fixed Fiedler vector,
  but `W` is **not single-valued when `λ₂` is degenerate** (the ~0.7 residual in the
  random check) — a proof must take the worst (or a convenient) vector in the
  `λ₂`-eigenspace. Numerical `λ₂`, `f`. Families verified to machine precision.
