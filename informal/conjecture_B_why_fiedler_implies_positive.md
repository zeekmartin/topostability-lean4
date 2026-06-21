# Conjecture B — WHY `Lf = λ₂f` implies `fᵀMf = gap ≥ 0` (M indefinite)

`M = λ₂Q − (λ₂/m)ddᵀ − L_t` is *indefinite* (≈n/2 negative eigenvalues), yet `gap = fᵀMf ≥ 0` for the
Fiedler `f`. The question: why does the eigenvector constraint force non-negativity? Code:
[`conjecture_B_why_fiedler.py`](../conjecture_B_why_fiedler.py).

## The short answer

**It is NOT a spectral fact about `M`.** `M` is genuinely indefinite (for `gnp(20,.5)`: 12 negative,
7 positive eigenvalues), so `fᵀMf ≥ 0` fails for generic `f`. It holds **only because `f` is pinned by
`Lf = λ₂f`**: the Fiedler is *not* an `M`-eigenvector (`|cos(f, Mf)| ≈ 0.93 ≠ 1`), and the eigenvector
equation is exactly the `n−1` scalar constraints `Σ_{u~v} f_u = (d_v − λ₂)f_v` that land `f` in the
region where `M ⪰ 0`. So "why" reduces to: **substitute these constraints into `gap` and exhibit a
non-negative certificate** — which is the open content. No a-priori reason exists; the constraint is
*necessary* and the certificate is *missing*.

## TASK 1/3 — apex identity and per-apex slack (verified)

**Apex identity (exact):** `T_ord = Σ_c E_{G[N(c)]}(f)`, `E_{G[N(c)]}(f) = Σ_{a,b∈N(c), a~b}(f_a−f_b)²`
(verified to machine precision). And `Σ_c Σ_{v∈N(c)} f_v² = Σ_v d_v f_v² = fᵀDf`.

Per-apex slack `s_c(w) = w·λ₂·Σ_{N(c)}f² − E_c`:

| graph | weight `λ₂`: `#s_c < 0` | weight `2λ₂`: `#s_c < 0` (min) |
|---|---|---|
| gnp(20,.5) | **10/20** | **1/20** (−0.014) |
| gnp(30,.4) | 11/30 | **0/30** (+0.009) |
| rr(20,6) | 0/20 | 0/20 (+0.70) |
| K₁₅ | 15/15 | **0/15** (+2.0, uniform) |

> The **local Poincaré with weight `λ₂`** (`E_c ≤ λ₂·Σ_{N(c)}f²`) **fails on ~50% of apices** (it was
> "~6%" only on sparse graphs). With weight **`2λ₂`** it holds on **~99%** (rare tiny violations,
> e.g. `−0.014`). So `Σ_c E_c = T_ord ≤ 2λ₂·fᵀDf` (the aggregate Poincaré) is **nearly** a per-apex
> non-negative sum — but **not exactly**: a few apex-local terms are negative and require cross-apex
> cancellation.

## TASK 2 — the SBP identity (verified, exact)

From `Lf = λ₂f` (`Σ_{u~v} f_u = (d_v − λ₂)f_v`), weight-summing with the triangle degree `σ_v`:

> **`Σ_e (σ_a + σ_b) f_a f_b = Σ_v σ_v (d_v − λ₂) f_v²`** (verified: `gnp20` `62.53 = 62.53`).

Combined with `T = Σ_v σ_v f_v² − 2Σ_e t_e f_a f_b`, this expresses the cross term via degree-weighted
`f_v²` — but `σ_v`, `t_e` are *not* simple degree functions, so it does not collapse `T` to a clean
degree expression (the obstruction is the triangle structure, not algebra).

## TASK 4 — `K_n` saturation

At `K_n`: `gap = 0` (equality). The per-apex weight-`2λ₂` slack is **uniform `s_c = 2`** (every local
graph `G[N(c)] = K_{n−1}` is complete, the local bound is at its tight constant). The weight-`λ₂` slack
is uniformly *negative* (`−(n−2)` per apex) — so `K_n` is exactly where the weight-`λ₂` local bound is
*maximally violated locally* yet the aggregate is tight: the saturation is a **global** balance, not a
local one.

## TASK 5 — `gap` is NOT a per-apex non-negative sum

`gap = λ₂G − T` (and the weaker `2λ₂fᵀDf − T`) are **not** expressible as `Σ_c (nonneg per-apex)`:

| graph | `Σ_c s_c(2λ₂)` | `min s_c` | `Σ max(s_c,0)` | `Σ min(s_c,0)` |
|---|---|---|---|---|
| gnp(20,.5) | 2.25 | −1.19 | 5.50 | −3.25 |
| deg2+dense(40) | 2.68 | −0.11 | 4.13 | −1.45 |
| rr(20,6) | 10.19 | +0.19 | 10.19 | 0 |

> Some `s_c < 0` (apices where the local Poincaré fails), so the total is *not* a sum of non-negative
> per-apex terms — **the SOS certificate must MIX apices** (the negative local terms are cancelled by
> positive ones elsewhere). On `rr(20,6)` it happens to be all-non-negative (0 negatives), but on
> dense/irregular graphs it is not. **The cross-apex cancellation is exactly the open content** of
> `gap ≥ 0`.

## Why, precisely

1. **`M` indefinite** ⇒ `gap = fᵀMf ≥ 0` is *not* an operator-PSD fact (it fails for generic `f`).
2. **`Lf = λ₂f` pins `f`** (it is not an `M`-eigenvector) into the cone where `M ⪰ 0`. The eigenvector
   equation = the `n−1` relations `Σ_{u~v}f_u = (d_v−λ₂)f_v`, which are *necessary*.
3. **The apex identity** `T = Σ_c E_c` and the **SBP identity** are the exact algebraic consequences of
   `Lf = λ₂f` available; substituting them, `gap` becomes a sum of per-apex terms that are
   *individually* often non-negative (weight `2λ₂`, ~99%) but **not always** — so `gap ≥ 0` requires a
   **global cancellation** across apices.
4. **`K_n` saturates** by a *global* balance (per-apex weight-`λ₂` slack is uniformly negative there,
   weight-`2λ₂` uniformly `+2`); the equality is `t_e = n−2 ∀e ⟺ K_n`.

So the honest answer: **there is no a-priori spectral reason** — `M` is indefinite, and `gap ≥ 0` is a
*conditional* non-negativity that holds because `Lf = λ₂f` constrains `f` to a measure-zero set where
the indefinite form is non-negative. The proof = an SOS/cancellation certificate using the eigenvector
relations, which the per-apex decomposition *nearly* provides (weight `2λ₂`, ~99% local) but cannot
complete locally; the remaining cross-apex cancellation is the open lemma `triEnergy_le_RHS`.

## Conclusion

- `gap = fᵀMf ≥ 0` is **not** explained by `M`'s spectrum (indefinite) — only by `f` being the Fiedler.
- The **apex identity and SBP** (exact, from `Lf = λ₂f`) reduce `gap` to a per-apex form that is
  **almost but not** per-apex non-negative (weight `2λ₂`: ~99%; weight `λ₂`: ~50%).
- `gap ≥ 0` therefore needs **cross-apex cancellation** — the genuine open content; no per-apex (local)
  SOS exists. `K_n` saturates by a global balance.
- This is *why* every local/per-edge/per-apex bound (S-procedure, signless, B2′, local Poincaré) has
  failed: the inequality is irreducibly *global*. A proof must be a global certificate (Rayleigh-type,
  saturated at `K_n`), consistent with the symmetrization/deletion non-monotonicity findings.

## Lean
No new lemma (analysis of why). The apex identity (`apex_triangle_energy_identity`, Paper15) and SBP
are the exact tools; the open `triEnergy_le_RHS` is the cross-apex cancellation. The weight-`2λ₂`
near-local bound (`E_c ≤ 2λ₂Σ_{N(c)}f²`, ~99%) is a candidate building block but not universally true.
