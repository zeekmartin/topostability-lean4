# Conjecture B — the scalar TYPE A partition inequality (block-flatness too lossy)

Focus on `maxt_port·D_port + maxt_core·D_core ≤ RHS` (`RHS = 2λ(2·degQuad − λ − degLin²/mE)`, ordered
Dirichlets). **Result: the inequality holds 19/19 (max ratio 0.935) but does NOT admit a clean
block-flatness proof — the `λ_max(L_H)` Rayleigh factor in `D_core ≤ λ_max·‖f_H−mean‖²` eats the 0.065
margin (sufficient condition holds only 17/19), and composing with `‖f_H−mean‖² ≤ src²/(γ−λ)²` loses
~60 % (9/19). At the worst case the port and core terms are balanced (0.47 each), so neither can be
dropped. The scalar with the *exact* Dirichlets is the smallest remaining inequality.** Code:
[`aggregate_typeA_scalar.py`](../aggregate_typeA_scalar.py).

## TASK 1/2 — measured quantities and term split

| graph | ratio | portTerm/RHS | coreTerm/RHS | maxt_port | maxt_core | γ/λ |
|---|---|---|---|---|---|---|
| **deg2+dense(80,.85)** | **0.935** | **0.467** | **0.468** | 1 | 67 | 28 |
| deg2+dense(60,.85) | 0.920 | 0.457 | 0.463 | 1 | 50 | 21 |
| deg2+dense(80,.6) | 0.830 | 0.459 | 0.371 | 1 | 41 | 19 |
| twin-port `K₈₀` d2 | 0.510 | 0.170 | 0.340 | 1 | 80 | 79 |

> **At the worst case both terms are ≈ 0.47** — balanced. The port term (`maxt_port = 1` for deg2+dense,
> but `D_port` carries the bottleneck) and the core term (`maxt_core` large, `D_core` small/flat) each
> contribute ~half. Neither is negligible, so the proof must control both.

## TASK 3 — port term

`maxt_port ≤ δ − 1` (`= 1` for deg2+dense, `δ = 2`). `D_port ≤ λ` (total Dirichlet). But
`portTerm ≤ 2(δ−1)λ`, and `2(δ−1)λ/RHS = 2λ/(2λ(2degQuad−λ−S²/mE)) = 1/(2degQuad−λ−S²/mE)` which exceeds
1 on deg2+dense (`degQuad ≈ 2.4`, regime ii) — **`D_port ≤ λ` is too lossy** for the port term. The
actual `portTerm/RHS ≈ 0.46` uses the *exact* `D_port` (the bottleneck localisation).

## TASK 4 — core term via block flatness (TOO LOSSY)

`D_core = (f_H−mean)ᵀ L_H (f_H−mean) ≤ λ_max(L_H)·‖f_H−mean‖²` (Rayleigh), and block flatness
`‖f_H−mean‖² ≤ src²/(γ−λ)²` (`poincare_on_block`). But:

| bound | tightness vs actual `D_core` |
|---|---|
| `D_core ≤ λ_max·‖f_H−mean‖²` (Rayleigh) | ~10 % overshoot (deg2+dense(80,.85): `0.032` vs `0.029`) |
| `D_core ≤ λ_max·src²/(γ−λ)²` (full chain) | **~60 % overshoot** (`0.047` vs `0.029`) |

> The `λ_max(L_H)` factor (= max core degree, large) is the obstruction: `f_H − mean` is NOT aligned with
> the top eigenvector of `L_H`, so the Rayleigh bound overshoots `D_core` by ~10 %. Block flatness
> (`‖f_H−mean‖² ≤ src²/(γ−λ)²`) adds further loss.

## TASK 5 — sufficient condition FAILS

| sufficient condition | holds |
|---|---|
| `portTerm + maxt_core·λ_max·src²/(γ−λ)² ≤ RHS` (block flatness chain) | **9/19** |
| `portTerm + maxt_core·λ_max·‖f_H−mean‖² ≤ RHS` (exact flat, Rayleigh only) | **17/19** |
| `portTerm + coreTerm ≤ RHS` (exact `D_core`) | **19/19** (max 0.935) |

> **No clean block-flatness sufficient condition.** Even with the *exact* `‖f_H−mean‖²`, the Rayleigh
> `λ_max` factor loses ~10 % and fails the 2 densest cases (the 0.935-margin is too thin). The full
> block-flatness chain fails 10/19.

## TASK 6 — smallest remaining scalar

The irreducible piece is the scalar with the **exact** Dirichlets:

> **`maxt_port·D_port + maxt_core·D_core ≤ RHS`** (19/19, max 0.935) — does not decompose into provable
> block-flatness / Fiedler pieces (both `D_port ≤ λ` and `D_core ≤ λ_max·flat` are too lossy). This is
> the residual content of `typeA_slack_ge_required`, reached from it via `triEnergy_le_of_partition`
> (previous round). It is sharper than the aggregate bound but its proof needs the *exact* spectral
> localisation of `f` (bottleneck on ports, flat on core), not the coarse `λ_max`/`λ` bounds.

## Conclusion

- The scalar holds **19/19** (max 0.935); **port and core terms are balanced (~0.47)** at the worst case.
- **Block-flatness is too lossy:** the `λ_max(L_H)` Rayleigh factor overshoots `D_core` by ~10 %
  (fails 2/19), the full `src²/(γ−λ)²` chain by ~60 % (fails 10/19). `D_port ≤ λ` also too lossy for the
  port term.
- **No clean sufficient condition** via standard bounds; the scalar with exact Dirichlets is irreducible.
  This is the precise residual of the TYPE A extremality — it needs the exact bottleneck/flat
  localisation, the same content as `gap/eff ≥ 1/3`.

## Lean
No code change: the scalar does not decompose into provable pieces (block-flatness bounds too lossy), so
no new sorry-free lemma closes or shrinks it. `triEnergy_le_of_partition` (previous round) already
reduces `typeA_slack_ge_required` to this scalar; the scalar itself is the irreducible TYPE A content.
3 sorrys unchanged (`aggregate_triangle_poincare`, `typeA_slack_ge_required`, `conjectureB`).
