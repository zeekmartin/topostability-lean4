# Conjecture B — TYPE A classification by terminal response

Classify TYPE A graphs by **terminal** (attachment-vertex resolvent) variables rather than core
structure, and find what controls `gap/eff`. `G = H + v₀` (`v₀~{a,b}`), `R = (L_H − λI)^{-1}` on
`1_H^⊥`, block `R₂` at `a,b`. Code:
[`conjecture_B_typeA_terminal_classification.py`](../conjecture_B_typeA_terminal_classification.py)
(72 TYPE A graphs: `gnp`/regular/circulant cores × varied attachments — `(0,1)`, hi-deg, lo-deg,
hi/lo — to spread the terminal variables; `gap/eff ∈ [1.60, 15.26]`).

Terminal variables: `γ = λ₂(H)`, `Δ, δ`; `eff_λ = (e_a−e_b)^⊤R(e_a−e_b) = R_aa+R_bb−2R_ab`
(`R_- = eff/2`); `R_+ = 𝟙^⊤R₂𝟙 = R_aa+R_bb+2R_ab` (symmetric/secular); `terminal_leverage = R_aa+R_bb`;
`asymmetry = |R_aa−R_bb|`; `common_defect = (N−2) − |N_H(a)∩N_H(b)|`; bottleneck ratio `λ/γ`.

## What controls `gap/eff` — single-variable correlations

| variable | `corr(gap/eff, ·)` |
|---|---|
| **`λ` (Fiedler eigenvalue / bottleneck sharpness)** | **+0.67** |
| `R_- = eff/2` | −0.63 |
| `terminal_leverage = R_aa+R_bb` | −0.63 |
| `R_+ = 𝟙^⊤R₂𝟙` | −0.62 |
| `γ·leverage` | −0.50 |
| `common_defect` | −0.48 |
| `λ/γ` (bottleneck ratio) | −0.45 |
| `γ` | +0.45 |
| `asymmetry = |R_aa−R_bb|` | −0.39 |
| `Δ/δ` (regularity) | −0.27 |

> **Primary control: `λ` (the bottleneck sharpness)**, `r = +0.67` — the single best predictor. The
> resolvent-magnitude variables (`R_-`, `leverage`, `R_+`) all sit at `≈ −0.63`: they are **redundant
> proxies** for the bottleneck (larger resolvent ⇔ weaker bottleneck ⇔ lower `gap/eff`), linked to `λ`
> by the secular `λ = 2n/((n−1)(1+R_+/2))`. **`common_defect` (−0.48)** and **`asymmetry` (−0.39)** are
> *secondary* modulators; regularity is weak (−0.27).

**No single terminal variable controls `gap/eff`.** Best single-variable linear fit is `λ`; the best
2-variable fit (`γ`, `γ·leverage`) still has residual `1.80` on a range of `13.7` (≈13%). The control
is genuinely **multi-factor** (bottleneck × resolvent magnitude × combinatorial defect).

## Clustering by terminal variables

**By bottleneck strength `λ/γ`:**

| cluster | n | `gap/eff` min / med / max |
|---|---|---|
| strong (`λ/γ < 0.1`) | 16 | 5.37 / **9.17** / 13.48 |
| mid (`0.1–0.3`) | 39 | 3.27 / 7.58 / 15.26 |
| weak (`0.3–0.5`) | 8 | 3.11 / 4.64 / 11.10 |
| borderline (`≥ 0.5`) | 9 | **1.60** / 4.67 / 9.55 |

> **`gap/eff` decreases as the bottleneck weakens** (`λ/γ ↑`): from median `9.2` (strong bottleneck,
> near-complete core) down to median `4.7` and **`inf = 1.60`** at the **TYPE A boundary** (`λ/γ → 0.5⁻`,
> the graph about to leave TYPE A as `λ → γ`). So the **worst case (smallest prefactor) is the
> marginal-bottleneck regime**, not the strong-bottleneck regime — the hardest TYPE A graphs sit at the
> edge of the class.

**By attachment asymmetry:** symmetric (`|R_aa−R_bb| < median`) → `gap/eff` median `8.46`; asymmetric →
median `6.81`, min `1.60`. Asymmetry **lowers** `gap/eff` (consistent with `r = −0.39`) but with large
overlap — a second-order effect, not a controller.

## Answer to the classification question

`gap/eff` is controlled, in order of strength, by:

1. **Bottleneck sharpness `λ` / `λ/γ`** (primary, `|r| ≈ 0.45–0.67`): stronger bottleneck
   (`λ/γ → 0`, near-complete) → `gap/eff → 10`; weaker (`λ/γ → 0.5`, boundary) → `gap/eff → 1.6`.
2. **Terminal leverage / resolvent magnitude** (`R_aa+R_bb`, `R_±`, `≈ −0.63`): redundant proxies for
   (1) via the secular.
3. **Common-neighbourhood defect** (`−0.48`, combinatorial) and **asymmetry** (`−0.39`): secondary
   modulators.
4. **Core bottleneck ratio `λ/γ`** is *the* organizing axis for clustering (monotone trend), but is
   *not* a clean controller on its own (`r = −0.45`; the worst cases cluster at its boundary).

**No terminal variable (or pair) determines `gap/eff`** to better than ~13% residual: the prefactor is
multi-factor, with the irreducible part again the full-spectrum response at the junction. The
classification *does* localize the hard cases — **the TYPE A boundary `λ/γ → 0.5⁻`** (marginal
bottleneck), where `inf(gap/eff) ≈ 1.6` — which is the regime any proof must control.

## Conclusion

- **Primary controller of `gap/eff`: the bottleneck sharpness `λ` (`r = +0.67`)**, with resolvent-
  magnitude variables as redundant proxies; `common_defect` and `asymmetry` secondary.
- **Clustering by `λ/γ` is monotone**: `gap/eff` falls from `~9` (strong/near-complete) to `inf ≈ 1.6`
  at the TYPE A boundary. The **hardest TYPE A graphs are at the edge of the class** (marginal
  bottleneck, `λ/γ → 0.5⁻`), not in its dense interior.
- **No single/pair terminal variable controls `gap/eff`** (residual ≈13%): the prefactor remains
  multi-factor and not a finite terminal invariant — consistent with the standing TYPE A obstruction.

## Lean
No new lemma (numerical classification). Standing content unchanged; see `CONJECTURE_B_STATUS.md`.
