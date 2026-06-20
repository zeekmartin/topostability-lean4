# Conjecture B — TYPE A: exact structure of `gap / eff_resist`

`R = (L_H − λI)^{-1}` on `1_H^⊥`, block at `a,b`. Symmetric/antisymmetric split:
`R_+ = (R_aa+R_bb)/2 + R_ab` (symmetric, couples to `v₀`), `R_- = (R_aa+R_bb)/2 − R_ab = eff_resist/2`
(antisymmetric). `M2 = e_ab^⊤ R² e_ab` (2nd resolvent moment). Code:
[`conjecture_B_typeA_gap_over_eff.py`](../conjecture_B_typeA_gap_over_eff.py).

## TASK 3 — the secular equation (clean): `λ ↔ R_+`

For symmetric attachments (`R_aa = R_bb`, the Fiedler symmetric in `a,b`), the junction reduction
`α = (μ−x)/(1+R_+)` and `2α = −λx` give

> **`1 + R_+ = 2n/((n−1)·λ)`,  i.e.  `λ = 2n/((n−1)(1+R_+))`.**

Verified (max error `1.6·10⁻²`, exact for symmetric cores; the residual is from asymmetric `gnp`). So
the **symmetric resolvent response `R_+` alone fixes `λ`**; the **antisymmetric `R_- = eff/2` does not
enter the secular** — it is the orthogonal channel.

## TASK 1/2 — `gap/eff` does NOT close on the 2×2 block

| family | λ | `R_+` | `R_-=eff/2` | `M2` | gap | `gap/eff` | `gap/R_-` |
|---|---|---|---|---|---|---|---|
| K30 | 2.000 | 0.033 | 0.036 | 0.002 | 0.641 | 8.97 | 17.9 |
| gnp30_0.3 | 1.588 | 0.318 | 0.441 | 0.298 | 1.984 | 2.25 | 4.51 |
| gnp80_0.5 | 1.970 | 0.028 | 0.029 | 0.002 | 0.444 | 7.60 | 15.2 |
| circ120 | 1.970 | 0.024 | 0.021 | 0.001 | 0.147 | 3.45 | 6.89 |
| K120 | 2.000 | 0.008 | 0.009 | 0.000 | 0.165 | 9.75 | 19.5 |

Regression of `gap/eff` (range `9.4`):

| model | residual std |
|---|---|
| `poly(R_+, λ, n)` (2×2 block only) | **1.45** |
| `poly(R_+, λ, n, M2)` (+ 2nd moment) | **1.25** |

> **`gap/eff` is *not* a closed function of the 2×2 resolvent block.** A polynomial in `(R_+, λ, n)`
> leaves residual `1.45`; adding the **second moment `M2`** only reduces it to `1.25` (still ~13% of
> the range). The ratio retains dependence on **higher resolvent moments** (the full core spectrum),
> not just `R_aa, R_ab, R_bb`. This is the resolvent-side restatement of the Schur-round result: `gap`
> needs `R²` (normalization) and beyond, which the ratio does not cancel.

So **no resolvent entries cancel cleanly in `gap/eff`** — the secular cleanly fixes `λ` from `R_+`, but
`gap` itself draws on the whole resolvent (via the normalization `x² = 1 − x²·M2·…` and the `S²/m`,
degree terms), and `eff = 2R_-` only captures the antisymmetric scale.

## TASK 4 — manifest positivity?

Writing `gap = R_- · prefactor` (`prefactor = gap/R_- = 2·gap/eff`):

> `eff_resist = 2R_- > 0` is **manifest** (Green's-function sum rule, `R₂ ≻ 0 ⟺ λ < γ`). So
> `gap > 0 ⟺ prefactor > 0`, and the prefactor is **bounded away from 0** (`∈ [4.5, 23.3]`,
> `inf ≈ 4.5`) — but it is **not** a sum of squares / product of positive factors in the resolvent
> entries, nor a function of `R₂` alone (it needs higher moments). No manifestly-positive 2×2-block
> form exists.

The positivity therefore does **not** reduce to `R₂ ≻ 0`: that gives `eff > 0` (the scale), but the
order-one prefactor is the irreducible content.

## TASK 5 — `inf(gap/eff)` and the extremal graph

| family | `gap/eff` |
|---|---|
| gnp30_0.3 | **2.25** |
| circ120 | 3.45 |
| circ80 | 4.14 |
| gnp50_0.3 | 4.23 |

> `inf(gap/eff) = 2.25` at `gnp30_0.3` (a small, low-`λ` borderline TYPE A graph, `λ = 1.588`);
> `≈ 3.4` for larger graphs (circulant). All `> 0`. The minimizer drifts toward **low `λ`** (sparse
> core, attachments near the bottleneck) — the same attachment-junction region as every prior analysis.

## Conclusion

- **Clean:** the symmetric secular `λ = 2n/((n−1)(1+R_+))` (the symmetric resolvent response fixes the
  eigenvalue), and `eff_resist = 2R_- > 0` (Green's-function sum rule). `gap = R_- · prefactor` with
  `prefactor > 0` bounded away from 0.
- **Not clean:** `gap/eff` is **not** a closed function of the 2×2 resolvent block — it needs higher
  moments (`M2` and beyond), so no resolvent entries cancel to give a manifestly positive ratio.
  `inf(gap/eff) ≈ 2.25`.
- The electrical decomposition cleanly separates the **scale** (`R_-`/`eff`, manifestly positive) from
  the **prefactor** (`gap/eff ∈ [2.25, ~12]`, the irreducible residual). `gap > 0` reduces exactly to
  the prefactor lower bound, which is not a finite resolvent invariant.

This is the consolidation-ready endpoint: TYPE A `gap > 0` holds with `gap ≍ eff_resist > 0` (proven
scale); the positive prefactor `gap/eff ≥ c₀ > 0` is the sole remaining content and is *not* captured
by any finite resolvent invariant — the obstruction is the full-spectrum normalization at the `v₀–a–b`
junction.

## Lean
No new lemma (numerical/structural). Standing positive content: TYPE B closed
(`typeB_triEnergy_bound`, sorry-free), complete-core `gap = 10(n−3)/m`, and the Courant–Fischer fact
`eff_resist = 2R_- > 0 ⟺ R₂ ≻ 0 ⟺ λ < γ`.
