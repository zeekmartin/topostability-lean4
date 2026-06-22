# Conjecture B — the 2×2 compression route (clean fact, but factor-2 insufficient)

Attack `λ + S²/m ≤ d_eff + 1` via the 2×2 compression `B` of `A` onto `span{f, 1/√n}`. **Result: the
compression satisfies `μ_min(B) ≥ −1` (46/46, tight at `K_n`) — a clean span{f,1} analogue of the
regular edge-block `μ₂(A) ≥ −1` — but it does NOT imply the target: `μ_min(B) ≥ −1` gives
`(B₁₁+1)(B₂₂+1) ≥ B₁₂²`, while the target needs `(B₁₁+1)B₂₂ ≥ 2B₁₂²` (a factor-2 gap). A 2×2 compression
is too coarse.** Code:
[`conjecture_B_2x2_compression_irregular.py`](../conjecture_B_2x2_compression_irregular.py).

## Setup

`B = [[B₁₁, B₁₂],[B₁₂, B₂₂]]` (compression onto orthonormal `{f, 1/√n}`):
`B₁₁ = fᵀAf = d_eff − λ`, `B₁₂ = S/√n`, `B₂₂ = 2m/n`. Target `λ + S²/m ≤ d_eff + 1`
`⟺ B₁₁ + 1 ≥ S²/m = 2B₁₂²/B₂₂ ⟺ (B₁₁+1)B₂₂ ≥ 2B₁₂² ⟺ det(B) ≥ B₁₂² − B₂₂`.

## TASK 1 — interlacing

`μ₂(A) ≥ μ_min(B)` (Cauchy interlacing, compression to 2-dim): **holds 46/46** — but this is an *upper*
bound on `μ_min(B)`, not directly useful for the target.

## TASK 2/3 — the clean fact `μ_min(B) ≥ −1`, and why it is insufficient

> **`μ_min(B) ≥ −1` holds 46/46, with `min = −1.000` exactly (at `K_n`).** For `K_n`, `A + I = J ⪰ 0`
> (rank-1), so `B + I` is PSD with `μ_min(B) = −1` on the `f`-direction (`S = 0`). This is the
> `span{f,1}` analogue of the regular edge-block `μ₂(A) ≥ −1`.

`μ_min(B) ≥ −1 ⟺ B + I ⪰ 0 ⟺ det(B+I) ≥ 0 ⟺ (B₁₁+1)(B₂₂+1) ≥ B₁₂²`. **But the target is
`(B₁₁+1)B₂₂ ≥ 2B₁₂²`** — strictly stronger (the factor `2(B₂₂+1)/B₂₂ > 2`). **Counterexample** (generic
2×2): `B₁₁=0, B₂₂=1, B₁₂=0.9`: `μ_min(B) = −0.53 ≥ −1` ✓ but `(B₁₁+1)B₂₂ − 2B₁₂² = −0.62 < 0` ✗. So

> **`μ_min(B) ≥ −1` does NOT imply the target** — a 2×2 compression loses a factor of 2.

The target *does* hold (46/46) because the graph-specific `B₁₂ = S/√n` is constrained relative to
`B₁₁, B₂₂` (degree–Fiedler coupling) — but that constraint is not captured by the 2×2 spectrum alone.

## TASK 4 — alternative compressions / corrections

| candidate | result |
|---|---|
| `μ_min(B) ≥ −1` (`span{f,1/√n}`) | **46/46** (clean, but factor-2 weak) |
| `span{f, d_centered}` compression `C`, `μ_min(C) ≥ −1` | **13/44** (fails) |
| `λ_min(D − ddᵀ/m | 1⊥) ≥ λ−1` | 45/46 (near-miss, prior round) |

No 2×2 variant cleanly implies the target; the `span{f,1}` one is the only one with `μ_min ≥ −1`
universal, and it is factor-2 short.

## TASK 5 — hard families

| graph | target slack | `μ₂(A)` | `μ_min(B)` | `μ_min(A)` |
|---|---|---|---|---|
| deg2+dense(80,.9) | 16.3 | 4.33 | 0.055 | −5.98 |
| twin-port `K₈₀` d2 | 2.91 | 2.16 | 1.37 | −2.83 |
| star12+8 | 7.40 | 2.21 | 0.00 | −3.27 |
| `K₃₀ − 10` | 44.2 | 0.62 | 0.56 | −2.62 |
| `K₁₂` | 0.0 | −1.0 | **−1.0** | −1.0 |

`μ_min(B)` is closest to `−1` (binding) on `K_n`; the target has large slack on irregular graphs (the
`B₁₂ = S/√n` coupling keeps it satisfied). `μ_min(B) ≥ −1` is the *tighter* constraint, yet still does
not force the (looser-on-these-graphs) target via the 2×2 spectrum.

## TASK 6 — cleanest lemma candidate (and its limitation)

> **"2×2 compression lemma" (clean, true, tight at `K_n`):** `μ_min(B) ≥ −1`, i.e. `A + I ⪰ 0` on
> `span{f, 1}`. *However, this is factor-2 insufficient for the target* `(B₁₁+1)B₂₂ ≥ 2B₁₂²`.

So the 2×2 compression route, like the matrix-PSD and Cauchy–Schwarz routes, **does not close the
irregular spectral inequality**. The factor-2 (from `2m = Σd`) means a *rank-2* certificate is too
coarse; the degree–Fiedler coupling `B₁₂ = S/√n` that saves the target lives in the full structure, not
the 2×2 spectrum. A **3×3 compression** onto `span{f, 1, w}` (with `w` an edge or `Af` direction) is the
natural next candidate — it could carry the extra constraint that recovers the factor 2.

## Conclusion

- **`μ_min(B) ≥ −1`** (span{f,1} compression of `A`) is a clean, true, `K_n`-tight fact — the irregular
  analogue of the regular `μ₂(A) ≥ −1` — but **factor-2 too weak** for `λ + S²/m ≤ d_eff + 1`.
- The 2×2 route is **insufficient** (a generic 2×2 with `μ_min ≥ −1` can violate the target); the
  target survives only via the graph-specific `B₁₂ = S/√n` coupling, which a 2×2 spectrum does not see.
- **Next:** a 3×3 compression (adding an edge / `Af` direction) to recover the factor 2 — the remaining
  structural lead.

## Lean
No new lemma. `μ_min(B) ≥ −1` is a candidate auxiliary (clean, formalizable as `A + I ⪰ 0` on
`span{f,1}`) but does not imply the target; the regular case (`triEnergy_le_RHS_regular`, edge-block
`μ₂(A) ≥ −1`) remains the proven instance. The irregular target needs a richer (≥3-dim) certificate.
