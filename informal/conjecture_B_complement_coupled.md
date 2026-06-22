# Conjecture B — the complement-coupled inequality

Analyze the target `Σ_e deficit_e·g_e² ≥ λ(Σ_{nonedge} h² + S²/m)` (= `gap ≥ 0`) using both
`L_G f = λf` and `L_Ḡ f = (n−λ)f`. **Result: an exact complement reindex
`gap = Σ_v mdeg_v D_v − Σ_c Ēbar_c − λ(Σ_{nonedge} h² + S²/m)`, a NEW aggregate inequality
`Σ mdeg_v D_v ≥ λΣ_{nonedge} h²` (holds despite per-non-edge failure), but still no per-non-edge or PSD
certificate.** Code:
[`conjecture_B_complement_coupled.py`](../conjecture_B_complement_coupled.py).

## TASK 5 — the complement row equation (verified)

From `L_Ḡ f = (n−λ)f` at vertex `u` (and `Σf = 0`):

> **`Σ_{v ≁ u} f_v = −(d_u + 1 − λ) f_u`** (verified to `≤5·10⁻¹⁵`).

The non-edge analogue of the `G`-row `Σ_{v~u}f_v = (d_u−λ)f_u`. The two are consistent
(`(d_u−λ)f_u − (d_u+1−λ)f_u = −f_u = Σ_{v≠u}f_v`).

## TASK 1/2 — exact complement reindex

`deficit_e = mdeg_a + mdeg_b − t̄_e` (`t̄_e = ` common non-neighbours of edge `e`). Swapping sums:

- `Σ_e (mdeg_a+mdeg_b) g_e² = Σ_v mdeg_v D_v` (`D_v = Σ_{b~v} g_{vb}²`, local Dirichlet) `=
  Σ_{nonedge {a,c}} (D_a + D_c)`.
- `Σ_e t̄_e g_e² = Σ_c Ēbar_c`, `Ēbar_c = Σ_{a,b∈N̄(c), a~b} g_{ab}²` (Dirichlet on the
  non-neighbourhood of `c`).

> **`Σ_e deficit_e g_e² = Σ_v mdeg_v D_v − Σ_c Ēbar_c`** (verified: gnp20 `90.14 − 23.91 = 66.23`),
> hence
> **`gap = Σ_v mdeg_v D_v − Σ_c Ēbar_c − λ(Σ_{nonedge} h² + S²/m)`** (verified, all graphs).

## TASK 3/4 — per-non-edge bound FAILS, but the aggregate holds

The natural per-non-edge bound (from `Σ mdeg_v D_v = Σ_{nonedge}(D_a+D_c)` vs `λΣ_{nonedge} h²`):

| graph | `#{(D_a+D_c) < λh²}` | `Σ mdeg_v D_v − λΣ_{ne} h²` (aggregate) |
|---|---|---|
| gnp(20,.5) | **19/97** | **+45.9** |
| gnp(30,.4) | 32/269 | +96.8 |
| gnp(20,.8) | 13/45 | +37.5 |
| rr(20,6) | 12/130 | +43.5 |
| deg2+dense(40) | **113/293** | +35.5 |
| cycle₂₀ | 26/170 | +1.95 |

> **Per non-edge, `D_a + D_c ≥ λh²` FAILS** (~20%, up to 39% on deg2+dense) — *no* per-non-edge
> certificate. **But the AGGREGATE `Σ mdeg_v D_v ≥ λΣ_{nonedge} h²` holds** (`+45.9, …, +1.95`, all
> positive). This is a genuine new *aggregate* inequality (the negative per-non-edge terms are
> cancelled). Yet it is not enough by itself: `gap = (Σ mdeg·D − λΣ_{ne}h²) − Σ_c Ēbar_c − λS²/m` —
> the non-neighbourhood Dirichlet `Ēbar_c` and `λS²/m` corrections must still be absorbed
> (gnp20: `45.9 − 23.9 − 1.06 = 20.97 = gap`).

## TASK 6 — PSD on the complement eigenspace is CIRCULAR

`f` is a *simultaneous* eigenvector of `L_G` (eig `λ`) and `L_Ḡ` (eig `n−λ`). For non-complete `G`,
`λ₂` is simple, so the relevant constrained subspace is again `span(f)`, and "`gap = fᵀMf ≥ 0` on the
complement eigenspace" reduces to `gap ≥ 0` itself — **circular**, exactly as for the `G`-eigenspace.
The complement coupling adds a *constraint* (`L_Ḡf=(n−λ)f`) but not an independent positivity
mechanism, because `f` lies in both eigenspaces simultaneously.

## Conclusion

- **Clean complement identities (new):** `Σ_{v≁u}f_v = −(d_u+1−λ)f_u`; `Σ_e deficit_e g_e² =
  Σ_v mdeg_v D_v − Σ_c Ēbar_c`; and the exact `gap = Σ mdeg_v D_v − Σ_c Ēbar_c − λ(Σ_{ne}h² + S²/m)`.
- **New aggregate inequality:** `Σ_v mdeg_v D_v ≥ λΣ_{nonedge} h²` (holds despite ~20% per-non-edge
  violations — the cross-non-edge cancellation works *here*). This is a strictly weaker, possibly more
  tractable, sub-statement; but `gap ≥ 0` needs the further corrections `Σ_c Ēbar_c + λS²/m`.
- **No per-non-edge or PSD certificate:** the per-non-edge bound fails, and the complement-eigenspace
  PSD is circular (`f` simultaneous eigenvector ⟹ `span(f)`).
- So the complement coupling, like the direct, apex, and edge views, yields **exact identities and one
  new aggregate inequality, but the final `gap ≥ 0` remains a global comparison** with no termwise
  certificate — consistent with every prior round (the inequality is irreducibly global, saturated at
  `K_n`).

The one genuinely new lever is the aggregate `Σ mdeg_v D_v ≥ λΣ_{nonedge} h²` (= `Σ_{nonedge}[(D_a+D_c)
− λh²] ≥ 0`): it holds with positive margin and is a cleaner target than `gap ≥ 0` (no `Ēbar`/`S²/m`),
worth a dedicated attempt — but it is *necessary, not sufficient* for `gap ≥ 0`.

## Lean
No new lemma. The complement row equation `L_Ḡf=(n−λ)f` (from `L_Ḡ = nI−J−L_G`, `f⊥1`) and the reindex
`Σ deficit·g² = Σ mdeg·D − Σ Ēbar` are clean, formalizable. The aggregate `Σ mdeg·D ≥ λΣ_{ne}h²` is a
candidate sub-lemma (verified, holds with margin); `gap ≥ 0` still needs the `Ēbar + λS²/m` corrections.
