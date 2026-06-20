# Conjecture B — TYPE A: incomplete dense cores as quasi-complete graphs

`G = H + v₀` (`v₀~{a,b}`), `H` a dense incomplete core on `N = n_H` vertices, viewed as `K_N` minus
edges. Code: [`conjecture_B_incomplete_dense_cores.py`](../conjecture_B_incomplete_dense_cores.py)
(84 quasi-complete TYPE A graphs: `K_N` minus `0–30%` random edges, `N = 20,30,40`).

## TASK 1 — missing-edge variables vs spectral quantities (Pearson `r`)

Missing-edge variables: `missing_edges`, `missing_inc_a/b = (N−1)−d_H(a/b)`,
`missing_common_ab = (N−2) − |N_H(a)∩N_H(b)|`, `symdiff_ab = |N_H(a)△N_H(b)|`.

| variable | gap | gap/eff | R″ | **C_attach** | C_dense |
|---|---|---|---|---|---|
| missing_edges | −0.22 | −0.28 | +0.29 | −0.83 | +0.63 |
| missing_inc_a | −0.14 | −0.47 | +0.37 | −0.87 | +0.68 |
| missing_inc_b | −0.14 | −0.58 | +0.38 | −0.92 | +0.86 |
| **missing_common_ab** | −0.19 | −0.51 | +0.36 | **−0.93** | +0.79 |
| symdiff_ab | −0.21 | −0.47 | +0.32 | −0.89 | +0.76 |

> **`C_attach` (the dominant negative term) has a strong *combinatorial* predictor:
> `corr(C_attach, missing_common_ab) = −0.93`** — the more common neighbours `a,b` are *missing*
> (vs the complete core, where `missing_common_ab = 0` and `C_attach = 0`), the more negative
> `C_attach`. This is the clearest combinatorial handle yet on the spectral obstruction term: the
> "spectral position" `f_a, f_b` of the attachments is largely set by how incomplete their shared
> neighbourhood is. `C_dense` correlates `+0.79` with the same variable (partial compensation).

But **`gap` itself correlates only weakly** (`−0.19`) — because `gap = R″ + C` is the small residual
of two terms that *both* track the missing-edge count and largely cancel (`R″: +0.36`, `C_attach:
−0.93`).

## TASK 2 — quasi-clique deletion: does gap drop below the complete-core value?

From `K_N`, deleting edges (keeping TYPE A):

| deletion type | gap trajectory | vs complete |
|---|---|---|
| **attachment-incident (`a–bulk`)** | `0.762 → 0.728 → … → 0.786` | **drops below**, then recovers |
| **bulk–bulk** | `0.762 → 0.769 → … → 0.810` | **stays ≥ complete** (monotone up) |

> Deleting **bulk** edges *raises* gap (the complete core minimises over bulk-bulk edges); deleting
> **attachment-incident** edges *lowers* gap below the complete-core value (then it recovers as
> `d_a, d_b` drop further). Confirms the monotonicity finding: the complete core is the bulk-minimiser
> but **not** the global minimiser — the attachment degrees are the non-monotone axis.

## TASK 3 — local incompleteness lemma (fails)

- **`gap(H) ≥ gap(K_N) + c·missing_common_ab/m`:** `corr(gap−gap_complete, missing_common_ab/m) =
  +0.78`, but `gap − gap_complete` is **negative in 18/84** cases (exactly the attachment-deletion
  graphs). So the candidate lower bound **fails** — `gap` can sit *below* the complete-core value.
- **`gap/eff ≥ c₀ + c₁·missing_common_ab/N`:** `corr(gap/eff, missing_common_ab/N) = −0.65`
  (*negative* — more missing ⇒ *lower* `gap/eff`), so the proposed `+c₁` direction is wrong.
- On these quasi-complete cores `gap/eff ∈ [5.9, 10.0]` (`c₀ ≈ 5.9` here; sparser cores reach `≈2.3`).

So no clean local-incompleteness lower bound: the missing-edge structure predicts the *obstruction
term* `C_attach` well, but not a positive *lower bound* on `gap` (the residual changes sign across the
attachment axis).

## TASK 4 — shifted resistance `R_λ`

`R_λ = (e_a − e_b)^⊤ (L_H − λI)^{-1} (e_a − e_b)`:

> `R_λ = eff_resist` **exactly** (max diff `2.8·10⁻¹⁷`), since `e_a − e_b ⊥ 1` (the null mode never
> enters). So `gap/R_λ = gap/eff_resist ∈ [5.9, 10.0]` (quasi-complete), `corr(gap/R_λ,
> missing_common_ab) = −0.51`.

`R_λ` adds nothing beyond `eff_resist`; the missing-edge variables predict `gap/R_λ` only moderately
(`r ≈ −0.5`).

## Conclusion

- **New combinatorial handle:** `C_attach ≈ −(const)·missing_common_ab` (`r = −0.93`). The dominant
  spectral obstruction term is largely determined by the **combinatorial** incompleteness of the
  shared neighbourhood of `a,b` — exactly the "quasi-complete" intuition. `C_attach → 0` as
  `missing_common_ab → 0` (complete core).
- **But the gap resists:** `gap = R″ + C` is the small residual; `R″` and `C_attach` *both* track the
  missing-edge count and nearly cancel, so `gap` correlates weakly (`−0.19`) and the local-
  incompleteness lower bound **fails** (gap dips below complete under attachment-edge deletion,
  18/84). The complete core minimises over **bulk** edges only.
- **`R_λ = eff_resist`** exactly; nothing new there. `gap/eff ∈ [5.9, 10]` on quasi-complete cores.

The quasi-complete view sharpens *what drives the obstruction term* (`C_attach ↔ missing_common_ab`,
combinatorial, `r=−0.93`) but the obstruction itself remains: the gap is the cancellation residual
`R″ + C_attach`, both of which scale with the same missing-edge count, leaving no missing-edge lower
bound. The attachment-degree axis (lowering `d_a, d_b`) is where gap drops below complete.

## Lean
No new lemma (numerical study). Standing positive content unchanged (TYPE B closed, complete-core
`gap = 10(n−3)/m`); see `CONJECTURE_B_STATUS.md`.
