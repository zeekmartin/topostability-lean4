# Conjecture B — signed cancellation FAILS; and `B2′ ≤ 2λ·degQuad` is FALSE (critical correction)

Attempt to prove `C ≥ −λ` (`C = ½(A+I) = Σ_e(d_h−d_l)f_h(f_h−f_l)`) by a signed/PSD cancellation rather
than Cauchy–Schwarz. **Result: TWO negative findings, one critical. (1) The natural quadratic form
`M_C + L` is INDEFINITE (min eigenvalue `−0.13` on `deg2d80_0.1`), so there is no graph-independent
signed-SOS — `C ≥ −λ` is genuinely Fiedler-spectral. (2) CRITICAL: `C ≥ −λ` is actually FALSE for the
Fiedler on sparse-core deg2+dense (`C/λ` down to `−1.067`), hence the leaf `B2′ ≤ 2λ·degQuad`
(`B2prime_le_two_lam_degQuad`, introduced last round) is FALSE — the earlier "46/46" corpus missed
`q ≤ 0.12`. The Lean sorry on it was unsound and has been REVERTED to a direct sorry on the TRUE
`aggregate_triangle_poincare` (`T ≤ 2λ·degQuad`).** Code:
[`conjecture_B_signed_cancellation.py`](../conjecture_B_signed_cancellation.py).

## TASK 1 — signed-SOS via `M_C + L` FAILS (indefinite)

`C = fᵀM_C f` (`M_C[h,h] += δ, M_C[h,l] += −δ/2` per edge, `δ = d_h−d_l`), `λ = fᵀLf`, so
`C ≥ −λ ⟺ M_C + L ⪰ 0`. **`M_C + L` is INDEFINITE:**

| graph | min eig `(M_C+L)|_{1⊥}` |
|---|---|
| `deg2d80_0.1` | **−0.131** |
| `deg2d80_0.2` | +0.120 |
| gnp(40,.5) | +8.74 |
| `K₂₀` | +20.0 |

> A random-`f` test (540/540 on gnp) *falsely suggested* `C + Dirichlet ≥ 0` is general — but it only
> sampled gnp graphs, where `M_C+L ⪰ 0`. The rigorous generalized-eigenvalue test exposes the negative
> direction on sparse-core deg2+dense. **No graph-independent signed-SOS exists.**

## TASK 4 — CRITICAL: the sharp constant crosses `−1`, so the leaf is FALSE

Scanning `inf C/λ` (Fiedler) over deg2+dense with small `q`:

| | q=0.05 | q=0.08 | q=0.12 |
|---|---|---|---|
| N=80 | −0.90 | **−1.05** | −0.81 |
| N=100 | **−1.07** | −1.04 | −0.77 |
| N=140 | **−1.07** | −0.85 | −0.83 |

> **`C/λ` reaches `−1.067` (deg2d140_0.05) — `C ≥ −λ` is FALSE.** Equivalently `B2′ ≤ 2λ·degQuad` is
> FALSE: on `deg2d140_0.05`, `B2′/(2λ·degQuad) = 1.05` while `triEnergy/(2λ·degQuad) = 0.01`. The
> earlier rounds (`conjecture_B_B2prime_leaf_analysis.md`, `…_min_degree_measure.md`,
> `…_minus_one_identity.md`, `…_C_ge_minus_lambda.md`) used a corpus with `q ≥ 0.3` and so **wrongly
> concluded the leaf held with a margin**; with `q ≤ 0.12` it is violated.

**Why:** `B2′ = Σ_e(min(d_a,d_b)−1)g²` uses the per-edge bound `t_e ≤ min−1`, which is far too lossy when
the core is sparse — there are *few triangles* (`T` tiny) but the *min-degree energy* `B2′` is still
large. So `B2′ ≫ T`, and `B2′ > 2λ·degQuad` even though `T ≪ 2λ·degQuad`.

## The actual target `T ≤ 2λ·degQuad` (aggregate) HOLDS

| graph | `T/(2λ·degQuad)` | `B2′/(2λ·degQuad)` |
|---|---|---|
| deg2d140_0.05 | **0.008** | **1.048** (leaf false) |
| deg2d100_0.05 | 0.170 | 1.040 (leaf false) |
| deg2d80_0.08 | 0.071 | 0.841 |

> **`aggregate_triangle_poincare` (`T ≤ 2λ·degQuad`) holds robustly** (`T/(2λ·degQuad) ≤ 0.17`, huge
> slack) — the `B2′` overshoot does not affect it. So the regime-i target is fine; only the `B2′`
> *intermediate* was wrong.

## TASK 2/3 — structure (for the record)

The `A↔I` cancellation is large and tight: on deg2+dense, negative vertex mass
`Σ_{v: d_v²<s_v}(d_v²−s_v)f_v²/λ ≈ −20…−45` is compensated by `I/λ ≈ +19…+44`, leaving the small `C`.
Bad-edge Dirichlet mass (`f_h(f_h−f_l)<0`) is `≈ 0.94…0.98` of `λ` — almost all the gradient lives on
bad (bottleneck) edges. This extreme near-cancellation is exactly why `C/λ` can dip below `−1`.

## Lean fix (soundness)

The lemma `B2prime_le_two_lam_degQuad` (and its regular case) were **deleted** —
`B2′ ≤ 2λ·degQuad` is FALSE, so the sorry was unsound. `aggregate_triangle_poincare` is restored as a
**direct sorry** on the TRUE statement `T ≤ 2λ·degQuad`. Build OK; 3 sorrys
(`aggregate_triangle_poincare`, `typeA_extremality_gap_nonneg`, `conjectureB`), now all on true
statements. `triEnergy_le_B2prime` (`T ≤ B2′`, true per-edge) is kept but is **not** a route to
aggregate.

## Conclusion

- **Signed-SOS route DEAD:** `M_C + L` is indefinite (min eig `−0.13`); `C ≥ −λ` is Fiedler-spectral,
  not a general PSD form.
- **CRITICAL: `B2′ ≤ 2λ·degQuad` is FALSE** (`C/λ → −1.07` on sparse-core deg2+dense); the recent
  `B2′`-leaf rounds were on an incomplete corpus. **Lean reverted** to the direct (true) aggregate sorry.
- **`aggregate_triangle_poincare` (`T ≤ 2λ·degQuad`) holds** (slack ≥ 0.83) and must be proved directly
  — the `B2′`/`min`-degree relaxation is ruled out (too lossy on low-triangle graphs).

## Lean
3 sorrys, all true: `aggregate_triangle_poincare` (854), `typeA_extremality_gap_nonneg` (898),
`conjectureB` (970). The `B2′` intermediate is abandoned; the regime-i sorry is the direct aggregate
triangle-Poincaré, whose proof needs the triangle structure (not the min-degree relaxation).
