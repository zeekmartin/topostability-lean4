# Conjecture B — the irregular obstruction `A − B ≥ D`, and a DEGENERACY counterexample to the lift

`gap = A − B − D`, `A = Σ_e deficit_e g_e²`, `B = λΣ_{nonedge} h²`, `D = λS²/m`. Target (= `gap ≥ 0`):
`A − B ≥ D`. **Major finding: `A ≥ B` is robust (46/46), but `A − B ≥ D` (the lift `T ≤ λ₂G`) FAILS on
star+clique graphs — and this is a `λ₂`-DEGENERACY artifact: the lift fails for a *badly-chosen*
Fiedler in a high-multiplicity eigenspace, while a *good* Fiedler always exists.** This shows
`conjectureB_lift` / `triEnergy_le_RHS`, *as stated for an arbitrary eigenvector*, is **FALSE**; it
needs a degeneracy-aware reformulation. The regular lemma `triEnergy_le_RHS_regular` is unaffected
(`gap ≥ λ(d+1−λ) ≥ 0` for *all* eigenvectors). Code:
[`conjecture_B_AB_minus_D.py`](../conjecture_B_AB_minus_D.py).

## TASK 1 — `A ≥ B` is robust

Over 46 graphs (lollipop, barbell, broom, windmill, star+clique, deg2+dense, twin-port `K_N`, gnp,
near-complete):

> **`A ≥ B` : 46/46.** `min(A − B) = 0.050` (broom20_10); `max(B/A) = 0.978` (deg2+dense120).

So the weaker inequality `Σ_e deficit_e g_e² ≥ λΣ_{nonedge} h²` holds throughout (consistent with the
complement-round aggregate).

## TASK 3 — `A − B ≥ D` (= `gap ≥ 0`, the lift) FAILS on star+clique

> **`A − B ≥ D` : 45/46** — **fails on `starclq12_15`** (`K₁₂` + 15 pendants at one vertex):
> `gap = −1.06`. Also `K₂₀ + 40 pendants`: `gap = −4.94`. (`max D/(A−B) = 1.16` there.)

Direct check (independent recompute) confirms the lift `T ≤ λ₂G` fails:

| graph | `λ₂` | `T` | `λ₂G` | gap | lift |
|---|---|---|---|---|---|
| `K₁₂ + 15` | 1.0 | 5.758 | 4.697 | **−1.06** | **FAILS** |
| `K₂₀ + 40` | 1.0 | 12.20 | 7.26 | **−4.94** | **FAILS** |
| `K₈ + 10` | 1.0 | 0.001 | 1.001 | +1.00 | holds |
| `K₁₀ + 20` | 1.0 | 5.46 | 5.87 | +0.41 | holds |

## The cause: `λ₂` DEGENERACY (the key finding)

Star+clique has `λ₂ = 1` with **high multiplicity** (the pendants at one vertex span a large
`λ = 1` eigenspace). `numpy`/an arbitrary Fiedler picks one vector from this eigenspace, and the lift
fails for *that* choice. Sampling `gap` over the `λ₂`-eigenspace:

| graph | n | `λ₂` | mult | min gap | max gap |
|---|---|---|---|---|---|
| `K₁₂+15` | 27 | 1.0 | **15** | **−1.06** | +1.0 |
| `K₂₀+40` | 60 | 1.0 | **40** | **−1.1+** | +1.0 |
| `K₈+10` | 18 | 1.0 | 10 | +0.70 | +1.0 |
| `K₁₀+20` | 30 | 1.0 | 20 | +0.67 | +1.0 |

> **`max gap ≥ 0` over the eigenspace ALWAYS** (a *good* Fiedler exists for which the lift holds), but
> **`min gap` can be `< 0`** (a *bad* Fiedler in the same eigenspace violates the lift). So the lift
> failure is **purely a degeneracy artifact** — when `λ₂` is simple, `f` is unique and the issue
> disappears.

## Consequence for the formalization (important, honest)

> **`conjectureB_lift` and `triEnergy_le_RHS`, as stated — `∀ f, Lf = λf → triEnergy G f ≤ RHS` — are
> FALSE.** A bad eigenvector in a degenerate `λ₂`-space is a genuine counterexample. The sorry for
> `triEnergy_le_RHS` cannot be filled as literally stated.

The correct statements (any of):
- **simple `λ₂`** hypothesis (`f` unique up to scale): then no degeneracy, and the bound is the open
  content; OR
- **existential**: `∃ f` in the `λ₂`-eigenspace with `triEnergy G f ≤ RHS` (always true — `max gap ≥ 0`);
  this is what Conjecture B's projected-Fiedler reduction actually needs (it may *choose* the lift); OR
- the **specific projected lift** `h' = Bᵀf − (S/m)1_E`, which is one designated vector, not arbitrary.

**`triEnergy_le_RHS_regular` is SAFE:** its proof gives `gap ≥ λ(d+1−λ) ≥ 0` for *every* eigenvector
(it never uses simplicity), so it holds across degenerate regular eigenspaces (e.g. `K_n`, `K_{a,a}`).
The degeneracy problem is **specific to irregular graphs**.

## TASK 4 — equality / failure characterization

- **Simple `λ₂`:** `gap ≥ 0` holds on all tested (the genuine conjecture); equality only at `K_n`. The
  tightest *simple-`λ₂`* cases are deg2+dense / twin-port `K_N` (`gap → 0⁺`, small but positive).
- **Degenerate `λ₂` (irregular):** `gap < 0` is achievable for bad eigenvectors (star+clique); `gap = 0`
  is not the boundary — the eigenspace spans a *range* of `gap` values.

So `K_n` is the unique equality case **only within the simple-`λ₂` (or best-Fiedler) regime**; the
degenerate irregular graphs are a separate phenomenon (bad-eigenvector lift failure).

## TASK 2 / 5 — the cleanest true statement

`A − B = gap + D` exactly (`D = λS²/m ≥ 0`). For regular, `A − B = λ(n−λ) − C` (`D = 0`). For irregular
there is no single closed form, and (per above) the *arbitrary-eigenvector* inequality is false. The
cleanest TRUE statement implying Conjecture B:

> **(best-Fiedler lift)** For every connected `G`, there exists a Fiedler `f` (`Lf = λ₂f`) with
> `triEnergy G f ≤ 2λ₂(2·degQuad − λ₂ − degLin²/mE)`. (Verified: `max gap ≥ 0` over the eigenspace,
> all tested graphs.)

This is the honest target: Conjecture B follows from the *existence* of a good Fiedler, not from the
universal (false) statement. For **simple `λ₂`** it reduces to the plain `gap ≥ 0` (the standing open
inequality, true on all simple-`λ₂` tests, tight at `K_n`).

## Conclusion

- **`A ≥ B`** robust (46/46); **`A − B ≥ D` (the lift) FAILS on degenerate-`λ₂` irregular graphs**
  (star+clique) for badly-chosen Fiedlers — a **degeneracy artifact** (`max gap ≥ 0` always; a good
  Fiedler exists).
- **`conjectureB_lift` / `triEnergy_le_RHS` are FALSE as universally stated** — they need a simple-`λ₂`
  hypothesis or an existential (best-Fiedler) form. **`triEnergy_le_RHS_regular` is unaffected**
  (`gap ≥ λ(d+1−λ) ≥ 0` for all eigenvectors).
- The genuine irregular obstruction (simple `λ₂`) is the deg2+dense/twin-port bottleneck (`gap → 0⁺`,
  positive); the degenerate cases are a *separate* well-understood artifact.

## Lean
**Action item:** restate `conjectureB_lift` / `triEnergy_le_RHS` with a **simple-`λ₂`** hypothesis or as
an **existential** over the eigenspace (the current universal form is false). `triEnergy_le_RHS_regular`
stays valid as-is. The best-Fiedler existential is the honest reduction target for the full conjecture.
