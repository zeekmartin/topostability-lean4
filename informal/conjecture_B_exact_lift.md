# Conjecture B — the exact lift bound and the restricted Ritz spectrum

Returning to the exact lift route (abandoning the false min-degree lock). Operator
identities (Lean-verified, `edgeLift`/`triangleGraph`): `L_t = B·L_{T(G)}·Bᵀ`,
`D+A = BBᵀ`. For `φ⊥d`, `h=Bᵀφ`: `φᵀL_tφ = hᵀL_{T(G)}h`, `φᵀ(D+A)φ = hᵀh`. So

> `μ(G) = min_{φ⊥d} φᵀL_tφ/φᵀ(D+A)φ = ` **MIN** ` Ritz value of L_{T(G)} on
> U_d := range(Bᵀ|_{d⊥})` (an `(n−1)`-dim subspace of `ℝ^E`, all `⊥ 1_E`),

with Cauchy interlacing `λ₂(T) ≤ μ(G)`, and **B holds (connected non-bipartite G)
if `μ(G) ≤ λ₂(G)`**. Code:
[`conjecture_B_exact_lift.py`](../conjecture_B_exact_lift.py). 704 graphs incl. the
lock-breaking "degree-2 vertex + dense background" family.

**Two conclusions.**
1. **A correction:** the proposed target "bound the restricted spectral radius
   `λ_max(L_{T(G)}|_{U_d}) ≤ λ₂`" (the "for all `φ⊥d`" statement) is **FALSE** —
   the restricted radius is **2–11× λ₂**. B needs the **minimum** Ritz value
   `μ ≤ λ₂`, not the maximum.
2. **The exact reformulation is correct but gives no shortcut:** `μ ≤ λ₂(G)` holds
   100% (incl. the hard family), but `μ ≈ λ₂(T)` (within 9%), so `μ ≤ λ₂(G)` is
   essentially `λ₂(T) ≤ λ₂(G)` *restated* — the operator identity faithfully
   re-encodes B without reducing it.

---

## Min vs max Ritz value on `U_d`

| statement | holds | meaning |
|---|---|---|
| **(a) `μ = MIN Ritz ≤ λ₂(G)`** | **100%** | the correct target ⇒ B; holds everywhere |
| **(b) `MAX Ritz ≤ λ₂(G)`** | **1%** | the "for all φ" / spectral-radius target — **FALSE** |
| (c) projected-Fiedler `R_T(h') ≤ λ₂(G)` | 98% | the natural fixed test vector — fails ~6% on hard family |
| interlacing `λ₂(T) ≤ μ` | 100% | (guaranteed) |

magnitudes:

| ratio | median | max |
|---|---|---|
| **MAX Ritz / λ₂(G)** | **2.24** | **11.45** |
| μ / λ₂(G) | 0.503 | 1.000 |
| (μ − λ₂(T)) / λ₂(T) | **0.091** | 1.86 |

By family (μ≤λ₂ | maxRitz≤λ₂ | R_T≤λ₂ | med μ/λ₂ | med maxRitz/λ₂):
- `gnp`: 100% | 1% | 100% | 0.58 | 2.00
- `WS`: 100% | 4% | 100% | 0.43 | 1.70
- **`deg2+dense` (lock-breaker)**: 100% | 0% | **94%** | 0.50 | **7.41**

---

## What this means for the proof

### 1. The restricted spectral radius cannot be bounded by λ₂
The compression `Qᵀ L_{T(G)} Q` (`Q` = orthonormal basis of `U_d`) has its **top**
eigenvalue at `2–11× λ₂(G)` (median 2.24; up to 7.4× on the hard family). So:
- the operator inequality **`L_t ⪯ λ₂(G)·(D+A)` on `d⊥` is FALSE**;
- "`φᵀL_tφ ≤ λ₂·φᵀ(D+A)φ` for **all** `φ⊥d`" is false — the additive subspace
  `U_d` contains high-energy directions (lifts of high-frequency vertex functions)
  whose `T(G)`-Rayleigh quotient far exceeds `λ₂`.

So the question "bound the restricted spectral radius" has the answer **no** — and
it is the *wrong* quantity. B requires only the **minimum** Ritz value `μ ≤ λ₂`,
i.e. the existence of *one* good lift direction, not a bound on all of them.

### 2. `μ ≤ λ₂` holds — but `μ ≈ λ₂(T)`, so it is B restated
`μ ≤ λ₂(G)` is true on all 704 graphs (median `μ/λ₂ = 0.50`), **including the
deg-2+dense family that broke the min-degree lock** — confirming the exact lift
route survives where the relaxation failed. But Cauchy interlacing is **near-tight**:
`μ` sits within **9% (median)** of `λ₂(T)` above it. So `μ ≈ λ₂(T)`, and the
target `μ ≤ λ₂(G)` is essentially the conjecture `λ₂(T) ≤ λ₂(G)` itself, re-expressed
on the lift subspace. The operator identity `L_t = B L_{T(G)} Bᵀ` is an **exact
re-encoding**, not a reduction: it does not lower the difficulty.

### 3. No fixed test-vector recipe suffices
The projected-Fiedler lift `R_T(h') = fᵀL_t f /(fᵀ(D+A)f − S²/m)` (the canonical
single test vector) is `≤ λ₂(G)` only **98%** of the time (fails ~6% on the hard
family). So `μ ≤ λ₂` cannot be proved by *one* universal lift formula — on the hard
cases the optimal lift direction is some other `φ⊥d`, varying with the graph. A
proof must produce the minimizer adaptively, which is the genuine analytic core.

---

## Synthesis

The exact lift route is now precisely delimited:

- **Correct and surviving:** B ⟸ `μ(G) ≤ λ₂(G)`, where `μ` = smallest Ritz value of
  `L_{T(G)}` on the additive subspace `U_d = range(Bᵀ|_{d⊥})`. This holds 100% on
  all tested graphs, *including the family that refuted the min-degree lock*. The
  operator identities making this exact are Lean-verified.
- **Dead ends identified:**
  (i) bounding the restricted **spectral radius** by `λ₂` — false (radius `2–11λ₂`);
  (ii) any **single fixed lift** (e.g. projected Fiedler) — fails ~6% on the hard
  family;
  (iii) the **min-degree relaxation** (`W ≤ R''`) — false at scale (previous note).
- **The irreducible core:** because `μ ≈ λ₂(T)` (interlacing near-tight), proving
  `μ ≤ λ₂(G)` is equivalent in difficulty to B itself. The operator identity does
  not simplify it; it certifies that the lift subspace captures `λ₂(T)` (to ~9%) but
  the comparison `λ₂(T) ≤ λ₂(G)` remains the genuine content.

**Net:** the exact lift bound is the right object (it survives the lock's failure),
but it is a faithful restatement of B, not a crack. A proof needs the actual
adaptive minimizer / a direct comparison of `λ₂(T)` and `λ₂(G)` — there is no
operator-norm or fixed-test-vector shortcut.

### Caveats
- `λ₂`, `f`, Ritz values numerical; `U_d` built as `Bᵀ`(orthonormal basis of `d⊥`)
  then re-orthonormalized. Non-bipartite, `T(G)` connected. The hard family is the
  degree-2-vertex + dense-`G(n−1,q≈0.65)` construction (n=16–29). No new Lean this
  round — the operator identities `L_t=B L_{T(G)} Bᵀ`, `D+A=BBᵀ` are already verified.
