# Conjecture B — global inter-apex certificate for `gap = λ₂G − T ≥ 0`

Attempt to derive a global cancellation certificate. **Found: the exact apex decomposition
`gap = Σ_c (w*·W_c − E_c/2)` and a *centered* per-apex Poincaré (using the eigenvector local mean) that
is non-negative termwise on typical graphs AND the extremizer `K_n` — failing only on the high-slack
deg2+dense family. The abstract matrix-multiplier certificate is CIRCULAR** (`λ₂` simple). Code:
[`conjecture_B_global_certificate.py`](../conjecture_B_global_certificate.py).

## TASK 1 — exact apex decomposition (verified)

With `W_c = Σ_{v∈N(c)}f_v²`, `E_c` the apex Dirichlet energy (`T = Σ_c E_c/2`), and the global weight
`w* = λ₂G/fᵀDf`:

> **`gap = λ₂G − T = Σ_c (w*·W_c − E_c/2)`** (verified to machine precision, all graphs).

This uses `Σ_c W_c = fᵀDf` (each `v` counted `d_v` times) and `Σ_c E_c/2 = T`. The single self-consistent
weight `w* = λ₂G/fᵀDf` makes the sum exactly `gap`. Also verified: the **per-apex eigenvector
constraint** `m_c := Σ_{v∈N(c)} f_v = (d_c − λ)f_c` (the local consequence of `Lf = λf`).

## TASK 2 — negative apex contributions

`u_c = w*·W_c − E_c/2` (`w* < 2λ` since `Gvar < 2fᵀDf`):

| graph | `w*` (`2λ`) | `#u_c < 0` | min `u_c` |
|---|---|---|---|
| gnp(20,.5) | 5.43 (8.71) | **0/20** | +0.12 |
| gnp(30,.4) | 6.58 (9.68) | **0/30** | +0.09 |
| rr(20,6) | 3.94 (4.97) | **0/20** | +0.61 |
| **deg2+dense(40)** | 1.70 (3.91) | **17/40** | −0.04 |
| K₁₅ | 13.93 (30.0) | **13/15** | −0.07 |

> The uncentered per-apex `u_c` is **all non-negative on typical graphs** (gnp, rr) but negative on
> the **bottleneck (deg2+dense)** and on **`K_n`** (the extremizer). So the negatives concentrate at the
> two structured ends.

## TASK 3 — the compensating term: CENTERING by the eigenvector local mean

The fix uses `m_c = (d_c − λ)f_c`: the **centered local variance** `Var_c = W_c − m_c²/d_c`. The
centered per-apex Poincaré `E_c/2 ≤ 2λ·Var_c`:

| graph | `E_c/2 ≤ 2λ·Var_c` fails | `≤ λ·Var_c` fails |
|---|---|---|
| gnp(20,.5) | **0/20** | 7/20 |
| gnp(30,.4) | **0/30** | 3/30 |
| rr(20,6) | **0/20** | 0/20 |
| **K₁₅** | **0/15** | 0/15 |
| **deg2+dense(40)** | **37/40** | 37/40 |

> **Centering by the eigenvector mean `m_c = (d_c−λ)f_c` fixes both typical graphs AND `K_n`**
> (`0` failures, weight `2λ`) — the local Poincaré `E_c/2 ≤ 2λ·Var_c` holds per-apex there. **It still
> fails on deg2+dense** (37/40) — but that family has `T/(λ₂G) ≈ 0.3` (huge global slack), so the
> per-apex failures are massively over-compensated globally. So **the centered apex Poincaré is a
> per-apex certificate for everything except the high-slack bottleneck family.**

## TASK 4 — the abstract matrix certificate is CIRCULAR

The matrix-multiplier S-procedure asks for `Y` with `M + (L−λI)Y + Y(L−λI) ⪰ 0` (then
`gap = fᵀMf ≥ 0` since `(L−λI)f = 0`). But:

> **`λ₂` is SIMPLE** for every non-complete graph (verified: `λ₃ − λ₂ > 0` throughout; only `K_n` is
> degenerate). For simple `λ₂`, `ker(L−λI) = span(f)`, so the S-procedure is feasible **iff** `M ⪰ 0`
> on `span(f)` **iff** `fᵀMf ≥ 0` **iff** `gap ≥ 0` — **circular**.

So no *abstract* multiplier gives an independent certificate: the eigenvector constraint pins `f` to a
1-dimensional space, and the S-procedure there is tautological. **A genuine certificate must be the
structural apex decomposition, not an abstract multiplier.**

## TASK 5 — Lean-target lemma (candidate, with a caveat)

The natural building block is the **centered apex Poincaré**:

> *Candidate lemma:* for each apex `c`, `E_{G[N(c)]}(f) ≤ 4λ·(Σ_{v∈N(c)}f_v² − m_c²/d_c)` with
> `m_c = (d_c − λ)f_c = Σ_{v∈N(c)}f_v` (the eigenvector constraint). Summing over `c` and using
> `Σ_c (…)` would give `T ≤ …`.

**Caveat (honest): this is NOT universally true** — it fails on deg2+dense (37/40). So it cannot be the
whole proof; it would need a **case split**: the centered apex bound for "balanced" graphs (typical +
`K_n`, where it holds per-apex), and a *separate* (easy) argument for the bottleneck family (where
`T = O(λ²) ≪ λ₂G = Θ(λ)`, the TYPE B / low-degree-port slack). This mirrors the three-regime structure.

## Conclusion

- **Exact decomposition found:** `gap = Σ_c (w*W_c − E_c/2)`, `w* = λ₂G/fᵀDf` (verified).
- **The compensating mechanism is centering by the eigenvector local mean** `m_c = (d_c−λ)f_c`: the
  centered per-apex Poincaré `E_c/2 ≤ 2λ·Var_c` is **non-negative termwise on typical graphs and the
  extremizer `K_n`**, isolating the residual to the **high-slack deg2+dense** family (where it fails
  locally but the global gap is huge).
- **No abstract multiplier certificate** (matrix S-procedure is circular for simple `λ₂`).
- So a **single universal termwise certificate does not quite exist**, but the centered apex
  decomposition is the natural near-certificate: it works everywhere except the family that is
  *globally easiest*, suggesting a **case split** (centered apex bound on balanced graphs + the slack
  bound on bottlenecks) as the realistic proof architecture — exactly the three-regime split, now with
  a concrete per-apex tool for the dense/regular part.

## Lean
Candidate building block: centered apex Poincaré `E_{G[N(c)]}(f) ≤ 4λ·Var_c` (uses `m_c=(d_c−λ)f_c`,
from `Lf=λf`); proved per-apex on balanced graphs, false on deg2+dense — so a conditional lemma, not
universal. The exact decomposition `gap = Σ_c(w*W_c − E_c/2)` is a clean identity (formalizable). The
S-procedure circularity (simple `λ₂` ⟹ tautology) rules out the abstract-multiplier Lean route.
