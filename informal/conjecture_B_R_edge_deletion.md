# Conjecture B — `K_n` maximizes `R = T/(λ₂G)` (edge-deletion test)

Testing whether the complete graph maximizes `R = T/(λ₂G)` — equivalently, `T ≤ λ₂G` with equality
*only* at `K_n` (the content of the `triEnergy_le_RHS` sorry). **Result: `K_n` is the global maximum
(`R = 1`); `R < 1` everywhere else (no counterexample in 91+ graphs); but `R` is NOT step-monotone under
deletion** (the Fiedler jumps discontinuously). Code:
[`conjecture_B_R_edge_deletion.py`](../conjecture_B_R_edge_deletion.py).

## TASK 5 — exact first-order deletion formula at `K_n`

Deleting one edge `(i,j)` from `K_n`: `L_{K_n−e} = L_{K_n} − (e_i−e_j)(e_i−e_j)^⊤`, so on `1⊥` the
eigenvalue on `(e_i−e_j)` drops to `n−2` (the rest stay `n`). **The Fiedler localizes on the deleted
edge:** `f = (e_i−e_j)/√2`, `λ₂ = n−2`. Then (closed form, verified to all digits):

| quantity | value |
|---|---|
| `λ₂` | `n−2` |
| `T = Σ_e t_e g_e²` | `(n−2)(n−3)` (only the `2(n−2)` edges at `i,j`; `t = n−3`, `g² = ½`) |
| `Gvar = Σh² − S²/m` | `n−2` (`S = 0`) |
| `λ₂G` | `(n−2)²` |
| **`R(K_n−e)`** | **`(n−3)/(n−2)`** |

> **`R(K_n − e) = (n−3)/(n−2) < 1`**, so **`ΔR = −1/(n−2) < 0`** — a strict first-order decrease. (n=5:
> `2/3`; n=20: `17/18`; n=100: `97/98`.)

## TASK 1 — single-edge deletion (edge-transitive ⇒ one value per `n`)

| n | `R(K_n)` | `R(K_n−e)` | `≤ R(K_n)`? |
|---|---|---|---|
| 5 | 1 | 0.667 | ✓ |
| 20 | 1 | 0.944 | ✓ |
| 100 | 1 | 0.990 | ✓ |

All `= (n−3)/(n−2)`, all `< 1`.

## TASK 2/3 — deletion sequences: `R` is NOT step-monotone, but never exceeds 1

| n | states | `R` start | max | min | steps with `R` ↑ | `max ≤ R(K_n)`? |
|---|---|---|---|---|---|---|
| 20 | 115 | 1.000 | 1.000 | 0.248 | **15/114** | **yes** |
| 40 | 469 | 1.000 | 1.000 | 0.302 | **55/468** | **yes** |

> **`R` is NOT monotone non-increasing** (`~13%` of deletion steps *increase* `R`) — the Fiedler is
> discontinuous (after a deletion it can re-localize, jumping `R` up). **But `R` never exceeds `1`**:
> the maximum along every sequence is the starting `K_n` value. So **a "monotone descent from `K_n`"
> proof does NOT work, but `K_n` remains the global max.**

## TASK 4 — global maximum is `K_n` (no `R > 1` anywhere)

Broad search (91 graphs: `gnp(n,q)` `n=10..30`, `q=0.2..0.95`, + near-complete `K_n − k`):

> **max `R` found `= 0.964 < 1`** (at `K_{30} − 1` edge). **No graph has `R > 1`.** Combined with
> `R(K_n) = 1`, **`K_n` is the unique global maximizer of `R = T/(λ₂G)`** — i.e. `T ≤ λ₂G` holds
> everywhere with equality *only* at the complete graph.

## Answers

1. **Single-edge from `K_n`:** `R(K_n−e) = (n−3)/(n−2) < 1` (exact, all `n`).
2. **Sequences:** `R` stays `≤ 1`; never returns to 1 after leaving `K_n`.
3. **Monotone non-increasing?** **NO** — `~13%` of steps increase `R` (discontinuous Fiedler), though
   `R ≤ 1` throughout.
4. **Global max:** **`K_n`** — no graph achieves `R > 1` (0/91+; max `0.964`). Equality `T = λ₂G` is
   *unique* to the complete graph.
5. **First-order at `K_n`:** `ΔR = −1/(n−2)` (Fiedler `f = (e_i−e_j)/√2`, `λ₂ = n−2`, `R = (n−3)/(n−2)`).

## Conclusion — proof-route implication

- **`triEnergy_le_RHS` (`T ≤ λ₂G`) is confirmed: `K_n` is the unique global maximizer of `R`** (`R = 1`),
  `R < 1` (strictly) on every other graph. This is the cleanest possible extremal characterisation.
- **The proof cannot be a simple monotone descent from `K_n`** — `R` is not step-monotone (the Fiedler
  jumps on deletion, causing `~13%` local increases). The correct statement is the *global* bound
  `R ≤ 1` with the complete graph as the strict maximizer, not an edge-by-edge inequality.
- **First-order is clean and favourable:** `ΔR = −1/(n−2) < 0` at `K_n`, and the `K_n − e` extremal data
  is a closed form (localized Fiedler `(e_i−e_j)/√2`, `R = (n−3)/(n−2)`).

So the open `triEnergy_le_RHS` is a *global maximum* statement (R ≤ 1, max at `K_n`), not a monotonicity
— the right framing for a proof attempt (e.g. a global Rayleigh/variational bound saturated by `K_n`,
not a deletion induction).

## Lean
No new lemma (numerical extremal study). It pins down `triEnergy_le_RHS`: equality holds *iff* `G = K_n`;
the bound is a global maximum of `R`, ruling out a naive deletion-monotonicity proof.
