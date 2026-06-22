# Conjecture B — the λ₂-simple core (the irreducible inequality)

With the degeneracy dissolved by the trace route, the irreducible content is the **`λ₂`-simple case**
(`mult = 1`, `gap = trace = A − B − D`). This isolates the genuine obstruction and **rules out the
eigengap as a control parameter**. Code:
[`conjecture_B_simple_lam2_core.py`](../conjecture_B_simple_lam2_core.py) (42 simple-`λ₂` graphs).

## TASK 1/2 — simple-`λ₂` hard families, `gap = A − B − D`

Collected (all `λ₃ − λ₂ > 0`): deg2+dense (`n` up to 90, `q ∈ {0.4,0.6,0.8}`), twin-port `K_N`
(`d=2,3,4`), lollipop, barbell, random gnp, near-complete `K_n − k`. `gap > 0` on all 42
(`min gap = 0.13`). `A = Σ_e deficit_e g_e²`, `B = λΣ_{nonedge} h²`, `D = λS²/m`.

## TASK 3 — `B` saturates `gap`; tightest = dense bottleneck

| graph | gap | `B/A` | `D/A` | `gap/A` | eigengap |
|---|---|---|---|---|---|
| deg2+dense(90,.8) | 0.66 | **0.979** | 0.017 | **0.004** | 54.1 |
| deg2+dense(60,.8) | 0.76 | 0.968 | 0.025 | 0.007 | 36.9 |
| twinK₈₀ d2 | 1.95 | 0.916 | 0.060 | 0.024 | 1.98 |
| twinK₅₀ d2 | 2.11 | 0.868 | 0.090 | 0.042 | 1.97 |

> **`B = λΣ_{nonedge} h²` (complement signless energy) dominates** (`B/A = 0.87–0.98`); `D = λS²/m` is
> small (`≤ 0.09·A`). The tightest (`gap/A → 0.004`) are **high-density deg2+dense** — the bottleneck
> approaching the `K_n` equality limit.

## TASK 4/5 — the EIGENGAP is IRRELEVANT (key negative result)

| correlation | value |
|---|---|
| `corr(gap, λ₃−λ₂)` | **−0.23** |
| `corr(gap/A, λ₃−λ₂)` | **−0.40** |

> **The eigengap `λ₃ − λ₂` is NOT the control parameter — it is *anti*-correlated with `gap`.** The
> tightest graphs (`deg2+dense(90,.8)`, `gap/A = 0.004`) have a *large* eigengap (`54.1`), not a small
> one. So a bound `gap ≥ c(λ₃−λ₂)·Φ` is **false** (the tight cases have huge eigengap, tiny gap).
> Perturbation/near-degeneracy is **not** the source of the difficulty — the obstruction is **density**
> (approach to `K_n`), where `λ₂` is simple and the eigengap is large.

So `λ₂`-simplicity gives no extra leverage (eigengap irrelevant); the simple case is the *full* hard
inequality, with the complete graph as the limiting equality.

## TASK 4 — `A − B ≥ D` and no uniform multiplicative bound

- `A − B ≥ D` (= `gap ≥ 0`) holds on all 42 (min `gap = 0.13`); `min (A−B)/D = 1.23` (`D` never binds
  alone).
- **`min gap/A = 0.004`** (deg2+dense(90,.8)) → `0` as density `→ 1` (`K_n`). So **no uniform `c > 0`
  with `gap ≥ c·A`** — the infimum is the complete-graph limit, consistent with `K_n` being the unique
  equality (`gap = 0`).

## TASK 6 — clean lemma candidate (simple `λ₂`)

> **Lemma (simple `λ₂`, candidate).** For connected `G` with `λ₂` simple,
> `gap = A − B − D ≥ 0`, i.e. `Σ_e deficit_e g_e² ≥ λ(Σ_{nonedge} h² + S²/m)`, with equality iff
> `G = K_n`. The eigengap is irrelevant; the binding term is `B = λ·fᵀQ_Ḡf` (complement signless
> energy); the tight regime is high density.

This is the *irreducible* conjecture (no degeneracy, no eigengap shortcut). The **regular sub-case is
proved** (`triEnergy_le_RHS_regular`: `gap ≥ λ(d+1−λ) ≥ 0` via `λ ≤ d+1`, Cauchy interlacing). The open
content is the **irregular simple-`λ₂` dense case** (deg2+dense), where the regular identity
`gap = λ(n−λ) − C` breaks (`mdeg` varies, `D = λS²/m ≠ 0`).

## Honest status

- **Simple `λ₂` is the irreducible core** — `gap > 0` verified (42/42), tight at `K_n`.
- **Eigengap ruled out** (anti-correlated, `−0.40`): no `gap ≥ c·eigengap` bound; near-degeneracy is
  *not* the difficulty.
- **No uniform multiplicative bound** `gap ≥ c·A` (infimum `→ 0` at `K_n`).
- **Regular sub-case proved**; irregular dense (deg2+dense) is the residual open core, with `B`
  (complement signless energy) the binding term.

The simple-`λ₂` core is thus the original `gap ≥ 0` with all degeneracy/eigengap red herrings removed:
the proof must control `B = λ·fᵀQ_Ḡf` against `A = Σ deficit·g²` directly, with `K_n` the saturating
case — the regular argument (interlacing `λ ≤ d+1`) is the proven template; extending it to irregular
`λ ≤ Δ+1`-type bounds with the `λS²/m` correction is the next concrete target.

## Lean
No new lemma. Candidate: `gap ≥ 0` for simple `λ₂` (the irreducible core); `triEnergy_le_RHS_regular`
already proves the regular sub-case. The eigengap-irrelevance result rules out perturbation-based Lean
routes; the path is the deficit/complement inequality `A − B ≥ D` with the interlacing template.
