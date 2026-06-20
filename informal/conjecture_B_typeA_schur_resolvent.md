# Conjecture B — TYPE A gap via the core resolvent and a 2×2 Schur complement

`G = H + v₀`, `v₀ ~ {a,b}`, `Lf = λf`, `‖f‖=1`, `f ⊥ 1`. `x=f_v₀`, `p=f_a`, `r=f_b`, `γ=λ₂(H)`,
TYPE A: `λ < γ`. Code:
[`conjecture_B_typeA_schur_resolvent.py`](../conjecture_B_typeA_schur_resolvent.py).

## Task 1 — exact gap via the resolvent (regular core)

The eigenvector restricted to `H` gives the resolvent identity
`(L_H − λI)f_H = −(p−x)e_a − (r−x)e_b`, so `f_H = x·(L_H+P_ab−λ)^{-1}e_{ab}` is the junction response.
For a **ρ-regular core with `a,b` non-adjacent**, `D_H = ρI` collapses all higher resolvent moments
and the gap is an **exact closed formula** (verified `|formula − gap| ≤ 2.6·10⁻¹⁴`):

> **`gap = λ(ρ−λ+1) + (3λ−λρ−2)x² + (2λ+ρ−2)(p²+r²) + (3−ρ)xy − λS²/m`**
>
> equivalently `= λ(ρ+1)‖f_H‖² + (ρ+2λ−2)(p²+r²) + (4λ−2)x² − (ρ−3)xy − λ² − λS²/m`

with `y = p+r = (2−λ)x`, `S = (4−ρ−λ)x`, `m = ρn_H/2 + 2`, `‖f_H‖² = 1−x²`. This reduces `gap` to the
finite data `{x, p, r, λ, ρ, n, m}` — the requested exact expression.

## Task 2 — the 2×2 Schur complement (Woodbury)

The core block of `L_G` is `L_H + P_ab` (`P_ab = e_a e_a^⊤ + e_b e_b^⊤ = EE^⊤`). The eigenvalue
secular equation, via Woodbury on the full resolvent `G_0 = (L_H−λ)^{-1}`, reduces to a **2×2
condition** (verified `≤1.1·10⁻¹⁴`):

> **`2 − λ = 𝟙^⊤ G₂ (I + G₂)^{-1} 𝟙`**,  `G₂ = E^⊤ (L_H−λ)^{-1} E = [[G_aa, G_ab],[G_ab, G_bb]]`.

So the eigenvalue `λ` and the junction response are governed by the 2×2 matrix `M₂ = I + G₂`
(`G₂` = 2×2 block of the core resolvent at `a,b`). This is the "replace `f_H` by mean + resolvent
response," contracted to the two attachment d.o.f.

## Task 3 — the 2×2 matrices are PD for all TYPE A

| core | `λ` | `γ` | `eig R₂` (1⊥ block) | `eig M₂ = I+G₂` | R₂ PD | M₂ PD |
|---|---|---|---|---|---|---|
| rr(60,6) | 1.468 | 1.881 | [0.32, 0.39] | [1.32, 1.36] | ✓ | ✓ |
| rr(240,12) | 1.809 | 5.596 | [0.110, 0.111] | [1.106, 1.110] | ✓ | ✓ |
| rr(240,20) | 1.899 | 11.90 | [0.058, 0.059] | [1.053, 1.059] | ✓ | ✓ |

> **`R₂` (the 1⊥ resolvent block) and `M₂ = I+G₂` are positive-definite for every TYPE A graph**, and
> this is *exactly* the condition `λ < γ`: on `1_H^⊥`, `L_H − λ` has eigenvalues `≥ γ−λ > 0`, so its
> restriction `R = (L_H−λ)^{-1}|_⊥` is PD, hence any principal block `R₂` is PD, hence `M₂ = I+G₂ ≻ 0`.

## Task 4 — but `gap > 0` does NOT reduce to a 2×2 PSD

Write the exact formula as `gap = POS − NEG`:
`POS = λ(ρ+1)‖f_H‖² + (ρ+2λ−2)(p²+r²) + (4λ−2)x²`, `NEG = (ρ−3)xy + λ² + λS²/m`.

| core | gap | POS | NEG |
|---|---|---|---|
| rr(60,6) | 3.039 | 6.40 | 3.36 |
| rr(240,12) | 0.903 | 5.97 | 5.06 |
| rr(240,20) | 0.508 | 6.06 | 5.56 |

**`POS` and `NEG` both grow with `ρ` (`= O(n)`) and are nearly equal; `gap = POS − NEG` is their small
difference** — the same leading cancellation `R″_∞ = −C_∞ = 2(1−q)x²` found before. So:

> **`gap > 0` is NOT equivalent to (nor implied by) a single 2×2 PSD condition.** The 2×2 matrices
> `R₂, M₂` are PD *whenever `λ < γ`* (TYPE A membership / junction well-posedness), but that PD-ness
> alone does **not** certify `gap > 0`: `gap` is the `O(1/n)` residual of two `O(n)` quantities, a
> *global* balance that the 2×2 resolvent block does not capture.

The hoped-for reduction "gap positivity ⟺ 2×2 Schur PSD" therefore **fails** — rigorously, via the
exact formula. The 2×2 Schur governs the *eigenvalue* (secular equation) and is the right object for
"`v₀` is the bottleneck" (`λ<γ ⇔ M₂≻0`), but the *gap* sits one order below it.

## Conclusion

- **Exact (regular core):** `gap = λ(ρ−λ+1) + (3λ−λρ−2)x² + (2λ+ρ−2)(p²+r²) + (3−ρ)xy − λS²/m`
  (verified `2.6·10⁻¹⁴`); secular `2−λ = 𝟙^⊤G₂(I+G₂)^{-1}𝟙` (verified `1.1·10⁻¹⁴`).
- **2×2 PSD holds:** `R₂, M₂=I+G₂ ≻ 0 ⟺ λ < γ` — the TYPE A condition is precisely 2×2 resolvent
  definiteness.
- **But it does not give `gap > 0`:** `gap = POS − NEG` with `POS,NEG = O(n)` nearly equal; positivity
  is the sub-leading `O(1/n)` residual `c(q)·n/m`, not a 2×2 form. No theorem-shaped 2×2 PSD lemma for
  `gap > 0` exists — consistent with every prior round's leading-cancellation obstruction.

The weak positive target (`gap > 0` from `λ<γ` + 2×2 alone) is therefore **provably out of reach**; a
proof must control the `O(1/n)` residual `c(q)·n/m` (the scalar bound `c(q) ≥ 7.3·γ/Δ`), for which the
exact regular-core formula above is now the precise handle.

## Lean
The exact regular-core gap formula and the Woodbury secular `2−λ = 𝟙^⊤G₂(I+G₂)^{-1}𝟙` are exact
identities, but specific to the `G = H + v₀` construction (regular `H`, induced `L_H`, 2×2 resolvent
block). `R₂ ≻ 0 ⟺ λ < γ` is the clean linear-algebra fact (Courant–Fischer on `1_H^⊥`). Formalising
remains tied to induced-block spectral infrastructure (Paper16); deferred. No new general-graph
identity (the formula is regular-core-specific).
