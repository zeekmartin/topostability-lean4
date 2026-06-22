# Conjecture B — the spectral inequality `λ + S²/m ≤ d_eff + 1` (true, but Fiedler-specific)

Target: `λ + S²/m ≤ d_eff + 1` for the Fiedler `f`, equivalently **`fᵀAf ≥ S²/m − 1`** (since
`fᵀAf = d_eff − λ`), equivalently `fᵀ(D − ddᵀ/m)f ≥ λ − 1`. **Result: the bound is TRUE (46/46, tight at
`K_n` and deg2+dense), but it is NOT a for-all-`f` matrix inequality — the matrix `A + I − ddᵀ/m` is
*not* PSD on `1⊥` (fails 13/46). The bound genuinely uses the Fiedler equation `Af = (D−λ)f`; no
elementary matrix/Cauchy–Schwarz proof closes it.** Code:
[`conjecture_B_spectral_inequality_proof.py`](../conjecture_B_spectral_inequality_proof.py).

## TASK 1 — the target

`d_eff = fᵀDf`, `S = dᵀf`, `fᵀAf = d_eff − λ` (from `Lf = λf`). Target: `d_eff + 1 ≥ λ + S²/m`, i.e.

> **`fᵀAf ≥ S²/m − 1`**, i.e. `fᵀ(A + I − ddᵀ/m)f ≥ 0` (`‖f‖ = 1`).

**Verified: holds 46/46** (min slack `0.0` at `K₂₀`/`K₁₂`, tight; next-tight twin-port `K_N`, deg2+dense).

## TASK 5 — the matrix form FAILS (key negative)

`fᵀ(A + I − ddᵀ/m)f ≥ 0` for the *Fiedler*; is it `≥ 0` for *all* `f ⊥ 1` (which would give a clean PSD
proof)?

> **`λ_min(A + I − ddᵀ/m | 1⊥) ≥ 0` : only 13/46** (min `= −7.42` at deg2+dense(80,.6)). **The matrix
> `A + I − ddᵀ/m` is NOT PSD on `1⊥`** — the bound holds for the Fiedler but fails for other `f ⊥ 1`.
> So **the Fiedler-specificity is essential**; there is no generic matrix (S-procedure / Schur) proof.

The stronger sufficient condition `λ_min(D − ddᵀ/m | 1⊥) ≥ λ − 1` holds **45/46** (one near-miss) — so
even the centered-degree min-eigenvalue route just barely fails; the Fiedler beats the worst-case
direction on one graph.

## TASK 2/3 — Cauchy–Schwarz routes are too weak / invalid

- **TASK 2:** `S²/m ≤ 2·d_eff` (valid CS, 46/46) but the needed `2·d_eff ≤ d_eff + 1 − λ` holds **0/46**
  (`d_eff` large) — far too lossy.
- **TASK 3:** the *f-weighted* `S² ≤ fᵀ(D − d̄I)²f` is **not** a valid CS (holds only 23/46 — the
  correct CS is `S² ≤ Σ(d_v − d̄)²`, degree-variance, unweighted). The downstream
  `fᵀ(D−d̄)²f ≤ m(d_eff+1−λ)` holds 46/46 but rests on the invalid step. Route broken.

## TASK 4 — the Fiedler equation is the only handle

`Af = (D − λI)f` gives `fᵀAf = d_eff − λ` (the LHS) and `‖Af‖² = Σ(d_v−λ)²f_v² = fᵀA²f`. The promising
structure is the **2×2 compression of `A` onto `span{f, 1/√n}`** (orthonormal):

> `B = [[d_eff−λ, S/√n], [S/√n, 2m/n]]`, with Cauchy interlacing `μ₂(A) ≥ μ_min(B)`.

The target `fᵀAf ≥ S²/m − 1` is `B₁₁ + 1 ≥ 2B₁₂²/B₂₂`, i.e. `det(B) ≥ B₁₂² − B₂₂`. This compression is
the natural carrier of both the degree data (`B₂₂ = 2m/n`, `B₁₂ = S/√n`) and the Fiedler data
(`B₁₁ = d_eff − λ`), but a closing argument (relating `det(B)` / `μ_min(B)` to the bound) was not found.

## TASK 6 — corpus verification

| quantity | holds |
|---|---|
| **TARGET `fᵀAf ≥ S²/m − 1`** | **46/46** (min slack 0.0) |
| MATRIX `A+I−ddᵀ/m ⪰ 0` on `1⊥` | 13/46 (min −7.42) |
| `λ_min(D−ddᵀ/m|1⊥) ≥ λ−1` | 45/46 |
| CS `S²/m ≤ 2d_eff` (enough?) | valid 46/46, *enough* 0/46 |

Tight cases (min slack): `K_n` (degenerate, slack 0), twin-port `K_N` (simple, slack `→0`), deg2+dense
(simple). The bound is **saturated on the same families** as `gap = 0`/extremizer.

## Conclusion

- **The spectral bound `λ + S²/m ≤ d_eff + 1` is TRUE** (46/46), tight at `K_n` and the deg2+dense /
  twin-port bottleneck — exactly the gap-equality families.
- **It is NOT a generic matrix inequality** (`A + I − ddᵀ/m` not PSD on `1⊥`, 13/46) — Fiedler-specific.
  Elementary Cauchy–Schwarz routes are too weak (TASK 2) or invalid (TASK 3).
- The **regular case is proven** (`d_eff = d`, `S = 0`, `λ ≤ d + 1` via the 2×2 *edge* block
  interlacing). The **irregular case** uses the 2×2 `span{f,1}` compression `B` (interlacing
  `μ₂(A) ≥ μ_min(B)`), but the closing step is open.
- **Honest status:** this spectral bound is as deep as the irregular conjecture itself — it is a clean,
  true, tightly-saturated reformulation, but resists elementary (matrix/CS) proof; the Fiedler equation
  must be used, and the 2×2 compression `B` is the structural lead.

## Lean
No new lemma. The target `λ + S²/m ≤ d_eff + 1` (Fiedler) ⟹ `gap ≥ 0` (with the deficit bound,
`conjecture_B_irregular_effective_degree.md`). The regular instance is `triEnergy_le_RHS_regular`
(`λ ≤ d+1`). The general bound needs the `span{f,1}` interlacing compression — the next Lean target if
the closing argument is found; matrix-PSD and CS routes are ruled out.
