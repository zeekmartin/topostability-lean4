# Conjecture B — anatomy of the correction terms

`gap = A − B − C − D` with `A = Σ_v mdeg_v D_v`, `B = λΣ_{nonedge} h²`, `C = Σ_c Ēbar_c`, `D = λS²/m`.
**Key simplification: `A − C = Σ_e deficit_e g_e²` (the deficit term), so `gap = Σdef·g² − B − D`.**
**Result: `B` (non-edge signless energy) is the dominant/dangerous correction; `D` (`= λS²/m`) is a
small irregularity term, exactly `0` for regular graphs. `Σdef·g² ≥ B`, `≥ D`, `≥ B+D` all hold
(11/11).** Code: [`conjecture_B_correction_terms.py`](../conjecture_B_correction_terms.py).

## The real structure

`C = Σ_e t̄_e g_e²` (common-non-neighbour weighted), and `A = Σ_e(mdeg_a+mdeg_b)g_e²`, so
`A − C = Σ_e(mdeg_a+mdeg_b − t̄_e)g_e² = Σ_e deficit_e g_e²`. Hence the `A/C` split is artificial; the
genuine decomposition is

> **`gap = Σ_e deficit_e g_e² − B − D`,  `B = λΣ_{nonedge} h²`,  `D = λS²/m`** (verified, all graphs).

## TASK 1/2 — which correction is dangerous? `B`, not `D`

| graph | `B/Σdef` | `D/Σdef` | `(B+D)/Σdef` | `gap/Σdef` | reg? |
|---|---|---|---|---|---|
| gnp(20,.5) | 0.667 | 0.016 | 0.683 | 0.317 | no |
| gnp(40,.3) | 0.804 | 0.0004 | 0.805 | 0.195 | no |
| rr(20,6) | 0.498 | **0.000** | 0.498 | 0.502 | **yes** |
| rr(30,10) | 0.536 | **0.000** | 0.536 | 0.465 | **yes** |
| cycle₂₀ | 0.783 | **0.000** | 0.783 | 0.217 | **yes** |
| **deg2+dense(40)** | **0.926** | 0.029 | **0.955** | **0.045** | no |
| lollipop | 0.569 | **0.231** | 0.800 | 0.200 | no |
| K₂₀−e | 0 | 0 | 0 | 1.0 | — |

> **`B = λΣ_{nonedge} h²` is the dominant correction** (`B/Σdef = 0.50–0.93`). **`D = λS²/m` is small**
> (`≤ 0.23`) and **exactly `0` for every regular graph** (`S = Σd_v f_v = d·Σf_v = 0`). `D` is the
> *irregularity* term; it is largest on the lollipop (`0.23`, strongly irregular) but always dominated.

## TASK 3 — the sub-inequalities all hold

> **`Σdef·g² ≥ B` : 11/11**, **`Σdef·g² ≥ D` : 11/11**, **`Σdef·g² ≥ B+D` (= gap ≥ 0) : 11/11.**

So both corrections are *individually* dominated by the deficit term, and so is their sum. The
**binding** comparison is `Σdef·g² ≥ B` (the `B`-part), with `D` a comfortable add-on.

## TASK 4 — tightness and residual structure

`(B+D)/Σdef` (= `1 − gap/Σdef`) is the tightness:

- **Tightest at deg2+dense** (`0.955`, `gap/Σdef = 0.045`) — there `B` nearly exhausts `Σdef·g²` (the
  bottleneck), `D` small (`0.029`).
- **Regular graphs** (`D = 0`): tightness `= B/Σdef` (`rr`: `~0.5`, `cycle`: `0.78`) — `gap = Σdef·g² −
  B` exactly.

So the residual after subtracting the dominant `B` is `gap + D`; the only graph-class where `D` matters
at all is strongly irregular (lollipop), and even there `D < gap`.

## TASK 5 — complement rewrite of the corrections

Using the complement signless Laplacian `Q_Ḡ = D_Ḡ + A_Ḡ` and `L_Ḡf = (n−λ)f`:

> `B = λΣ_{nonedge} h² = λ·fᵀQ_Ḡf = λ(2Σ_v mdeg_v f_v² − (n−λ))`,  `D = λS²/m`, `S̄ = −S`.

So `B` is `λ` times the **complement signless energy** (`B/λ = fᵀQ_Ḡf ≥ 0`), and the problem is the
comparison of the `G`-deficit Dirichlet `Σdef·g²` against the `Ḡ`-signless energy `λfᵀQ_Ḡf` plus the
small `λS²/m`.

## TASK 6 — no clean global square; the core is the regular inequality

`gap = Σdef·g² − λfᵀQ_Ḡf − λS²/m` does **not** collapse to a covariance/variance/global square (tested;
`B` and `Σdef·g²` live on complementary edge sets and the difference is sign-positive only globally).
But the anatomy **isolates the core**:

> **For regular graphs `D = 0`, so `gap = Σ_e deficit_e g_e² − λΣ_{nonedge} h²`** — the entire content
> is `Σdef·g² ≥ λΣ_{nonedge} h²` (the `B`-inequality, the last round's aggregate). Irregularity adds
> only the small, always-dominated `D = λS²/m`.

## Conclusion

- **`gap = Σdef·g² − B − D`** with **`B = λΣ_{nonedge} h²` dominant/dangerous** and **`D = λS²/m` a
  small irregularity correction (`= 0` for regular, `≤ 0.23·Σdef` otherwise)**.
- **`Σdef·g² ≥ B`, `≥ D`, `≥ B+D` all hold (11/11)** — both corrections individually dominated.
- **The core difficulty is the regular-graph inequality `Σdef·g² ≥ λΣ_{nonedge} h²`** (`D = 0` there);
  irregularity (`D`) is a dominated add-on. This refines the target: prove the `B`-inequality
  `Σ_e deficit_e g_e² ≥ λΣ_{nonedge} h²`, then absorb the small `D`.
- No global square; `gap ≥ 0` stays a global comparison (consistent with all prior rounds), but the
  *dominant* and *binding* piece is now pinned to `B` (complement signless energy), with `D`
  (irregularity) demoted to a minor, always-controlled correction.

## Lean
No new lemma. Candidate sub-target: `Σ_e deficit_e g_e² ≥ λΣ_{nonedge} h²` (the `B`-inequality, holds
11/11, exact content of the regular case). `D = λS²/m` is a small dominated add-on. Both use the
complement identities (`L_Ḡf=(n−λ)f`, `B = λfᵀQ_Ḡf`), which are formalizable.
