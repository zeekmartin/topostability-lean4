# Conjecture B — TYPE A: equality case + resolvent invariant search

`G = H + v₀` (`v₀~{a,b}`). `T = Σ t_e g_e²`, `B2′ = Σ(min(d_a,d_b)−1)g_e²`, `gap = λ₂G − B2′`.
Equality in B (`T = λ₂G`) needs **both** `T = B2′` (per-edge `t_e = min−1`) **and** `B2′ = λ₂G`
(`gap = 0`, `R″+C = 0`). Code:
[`conjecture_B_typeA_equality_and_resolvent.py`](../conjecture_B_typeA_equality_and_resolvent.py)
(132 TYPE A graphs: random `gnp` cores + near-complete cores with reduced attachment degree).

## PART A — equality case

### TASK 1 — `T = B2′` slack `(min−1−t_e)·g_e²`, by edge class

| edge class | share of total slack |
|---|---|
| `v₀`-edges (`v₀–a`, `v₀–b`) | 0.169 |
| **attachment–bulk (`a–u`, `b–u`)** | **0.785** |
| bulk–bulk | 0.030 |

> The `T=B2′` slack is concentrated (**78%**) on the **attachment–bulk edges**. The `v₀`-edge slack is
> `>0` exactly when `a ≁ b` (then `t_{v₀a}=0 < 1 = min−1`): equality forces **`a~b`** (holds in
> 95/132). Tightness on `a–u` requires `t_{au} = min(d_a,d_u)−1`, i.e. `N(a)∖{u} ⊆ N(u)` for **every**
> neighbour `u` — a *locally complete* condition.

So `T = B2′` forces a **near-complete core** (`a~b` + nested attachment neighbourhoods).

### TASK 2/3 — can all equality conditions hold simultaneously?

- `min(B2′−T)` over TYPE A `= 0`, attained only by **near-complete cores** (2 of 132). Those have
  `gap = 0.641 > 0` — i.e. `B2′ < λ₂G` (the complete core is proved positive, `gap = 10(n−3)/m`).
- `min gap` over **all** TYPE A `= 0.505 > 0`.

> **Equality `T = λ₂G` is impossible in TYPE A.** It needs `T = B2′` *and* `B2′ = λ₂G`. But
> `T = B2′ ⟹` near-complete core `⟹ gap = λ₂G − B2′ > 0 ⟹ B2′ ≠ λ₂G` — contradiction. The two
> equality conditions are **incompatible** for a degree-2 bottleneck. Hence `B` is **strict** on TYPE A
> (the infimum `gap = 0` is not attained), consistent with `gap > 0`.

This is the equality-case answer (TASK 3): **no TYPE A equality graph exists.** It confirms strictness
but does not by itself lower-bound `gap` away from 0 (the open quantitative step).

## PART B — resolvent invariant search

### TASK 4 — invariants vs `c = gap·m/n` (Pearson `r`)

`R₂ = [[R_aa,R_ab],[R_ab,R_bb]]` = core resolvent `(L_H−λ)^{-1}|_⊥` at `a,b`.

| invariant | `corr(c, ·)` |
|---|---|
| **`1/eff_resist`** (`eff = R_aa+R_bb−2R_ab`) | **+0.837** |
| **`γ` (core gap)** | **+0.825** |
| `λ` | +0.476 |
| `gamma·(R_aa+R_bb)` | +0.408 |
| `eff_resist` | −0.550 |
| `θ = 𝟙ᵀR₂(I+R₂)⁻¹𝟙 = 2−λ` (secular) | −0.501 |
| `det(I+R₂)` | −0.417 |

> The best resolvent predictor of `c` is **`1/eff_resist`** (`r = +0.84`), essentially tied with the
> core gap **`γ`** (`r = +0.83`). Indeed `γ·eff_resist ∈ [0.92, 2.22]` (bounded), so
> `eff_resist ≈ Θ(1/γ)` and `1/eff ≈ Θ(γ)` — the two top predictors are the same quantity.

`eff_resist = R_aa + R_bb − 2R_ab = (1,−1)R₂(1,−1)ᵀ ≥ 0` is the **effective resistance between `a,b`**
in the resolvent metric; it is `> 0` strictly because `R₂ ≻ 0` (which holds **iff `λ < γ`**, the TYPE A
condition).

### TASK 5 — candidate resolvent lemma

> *Candidate:* "If `λ < γ` then `R₂ ≻ 0`, so `eff_resist > 0`, and (since `c ≈ C/eff_resist` with
> `C > 0`) `c > 0`, hence `gap > 0`."

The first three implications are **rigorous** (`λ<γ ⟹ R₂≻0 ⟹ eff>0` by Courant–Fischer). The last is
**not**: `c·eff_resist` is *not* constant (the correlation is `0.84`, not `1`), so `eff_resist` predicts
`c` but does not determine it. The unexplained residual is the same irreducible `O(1/n)` piece. So:

- **`eff_resist > 0` is the clean structural positivity *hint*** (it is exactly `R₂ ≻ 0 ⟺ λ < γ`), and
  it has the right sign correlation with `c`;
- but **no resolvent-only scalar certifies `gap > 0`** — `c` is a noisy (`r≈0.84`) multiple of
  `1/eff`, not an exact function of `R₂`.

## Conclusion

- **PART A:** the equality case is **empty** — `T = B2′` forces a near-complete core, which has
  `gap > 0`, so `T = λ₂G` never holds in TYPE A. `B` is strict (min gap `0.505 > 0`); slack lives on
  the **attachment–bulk** edges (78%) — again the `v₀–a–b` junction.
- **PART B:** the gap is best tracked by the **effective resistance** `eff_resist = R_aa+R_bb−2R_ab ≈
  1/γ` (and by `γ`), with `c ∝ 1/eff` at `r ≈ 0.84`. `eff > 0` follows rigorously from `R₂ ≻ 0`
  (`λ < γ`), giving the correct sign, but the correlation is imperfect so it is a predictor, not a
  certificate.

Both parts converge on the same picture: TYPE A has **no equality graph** and a gap that **scales like
`γ` / `1/eff_resist`**, positive throughout, but the exact value carries an `O(1/n)` residual no single
algebraic/resolvent scalar pins down — the obstruction remains the attachment junction.

## Lean
No new lemma (numerical study). `eff_resist > 0 ⟺ R₂ ≻ 0 ⟺ λ < γ` is the clean Courant–Fischer fact
underlying the resolvent positivity; standing positive content unchanged (TYPE B closed, complete-core
`10(n−3)/m`).
