# Conjecture B — variational attack on the reduced core `C + R″ ≥ 0`

Reduced (triangle-free) target: **`gap := C + R″ = λ₂G − B2′ ≥ 0`**, where
`R″ = λ₂(fᵀDf − λ₂ + 1 − S²/m)`, `C = Σ_{edges, h higher-deg}(d_h−d_l)f_h(f_h−f_l)`. With `f` the
Fiedler (`Lf = λ₂f`, `f ⊥ 1`, `‖f‖=1`), **Rayleigh minimality** gives, for *any* `φ ⊥ 1`,
`Q(φ) := φᵀ(L − λ₂I)φ ≥ 0`. A proof would write `gap = Q(φ) + (manifest nonneg)` for an explicit
`φ`. Code: [`conjecture_B_variational_core.py`](../conjecture_B_variational_core.py), 566 graphs.

## Verdict: the second-variation-of-a-natural-vector route is dead.

No natural degree-built perturbation `φ` yields `gap = Q(φ) + nonneg` (i.e. `rem := gap − Q(φ) ≥ 0`
universally); and at scale every natural `Q(φ)` *overshoots* the vanishing `gap`.

## TASK 1 — perturbation tests (project each `φ` to `1⊥`)

| `φ` | `rem = gap − Q(φ) ≥ 0` | min rem | corr(gap, Q) |
|---|---|---|---|
| `√D·f` (degree-order matched) | **352/566** | −1.02 | −0.14 |
| `Df`, `(D−λ₂)f`, `(D−d̄)f` | 122/566 | −159 | −0.01 |
| `L_W f` (C-divergence, `W=|d_a−d_b|`) | 22/566 | −3·10⁵ | −0.03 |
| `M_C f` (`M_C = ½diag(Ld)+½L_W`) | 20/566 | −8·10⁴ | −0.08 |
| `d`, `(Ld)·f` | ≤1/566 | −2·10⁵ | +0.67 / − |

(`Df`, `(D−λ₂)f`, `(D−d̄)f` give *identical* `Q` because they differ by multiples of `f` and `1`,
which contribute `0` to `Q` — minimality is blind to the `f`-component.) **No `φ` has `rem ≥ 0` on all
graphs.** The best is `√D·f` (the degree-order-matched perturbation), but it still fails on 214/566.
Even taking, per graph, the *smallest* candidate `Q`, it exceeds `gap` on 38% of graphs (median
min-`Q`/`gap` = 0.61). So no natural `φ` (nor the candidate span) gives a universal witness.

## TASK 2 — edge-divergence representation of `C` (exact, but overshoots)

`C` is a quadratic form: with `Ld = L·d` and the degree-discrepancy Laplacian `L_W`
(`W_ab = |d_a−d_b|`),

> **`C = fᵀ(½·diag(Ld) + ½·L_W) f = ½⟨Ld, f²⟩ + N = ½𝒜 + N`**  (exact, verified),

so the natural "divergence perturbation" is `φ = L_W f = div(W∇f)`. But `Q(L_W f)` is enormous
(`~ n³` on deg2+dense, see TASK 4) — the divergence of `f` weighted by `|Δd|` is a high-degree
object, nothing like the tiny `gap`. The operator `M_C` (so that `C = fᵀM_C f`) likewise gives a
useless `Q(M_C f) ~ n³`.

## TASK 3 — exact-identity search: none found

We sought `gap = Q(φ) + R` with `R` a recognizable nonnegative form (variance/Dirichlet) and `φ`
explicit. **No candidate has `rem ≥ 0` on all graphs**, so none yields such an identity. This
confirms the earlier finding (`conjecture_B2prime_variational.md`): `C + R″` is **not** the second
variation of any natural degree-built vector (full-span least-squares `R² < 0`).

## TASK 4 — scaling: why minimality is too lossy

On deg2+dense the gap vanishes, `gap ~ n^{−0.92}`, but the natural Rayleigh excesses do **not**:

| `φ` | `Q(φ)` scaling | vs `gap ~ n^{−0.9}` |
|---|---|---|
| `√D·f` | `~ n^{0.13}` (→ const ≈ 1.9) | overshoots by `O(1)` |
| `Df`, `(D−λ₂)f`, `(D−d̄)f` | `~ n^{1.04}` | overshoots by `O(n)` |
| `d`, `(Ld)·f` | `~ n^{3.0}` | overshoots by `O(n³)` |
| `L_W f`, `M_C f` | `~ n^{3.2}` | overshoots by `O(n³)` |

Even the *best-matched* `√D·f` has `Q → 1.9` while `gap → 0`: the Rayleigh excess of any natural `φ`
is bounded below by an `O(1)` (or growing) quantity, but `gap = R″ + C` is an `O(n^{−0.9})` near-
cancellation (`R″ → 0.71`, `C → −0.69`). **Minimality `Q(φ) ≥ 0` is far too lossy to certify a gap
this small** — the witness `φ*` achieving `Q(φ*) = gap` exists abstractly but is *not* a degree-
polynomial in `(d, f, λ₂)`; it is `gap`-dependent (circular).

## Conclusion

- **The direct variational attack fails.** No natural `φ ⊥ 1` (degree-weighted Fiedler `Df`,
  `√D·f`, degree-centered, the `C`-divergence `L_W f`, the `C`-operator `M_C f`, or `d`) gives
  `gap = Q(φ) + nonneg`; on 38% of graphs every candidate `Q` overshoots `gap`.
- **The obstruction is the smallness of `gap`.** `gap ~ n^{−0.9} → 0` on deg2+dense, while every
  natural `Q(φ)` is `Ω(1)` (and usually `→ ∞`). Second-variation of any natural vector overshoots a
  near-cancelling target. The required witness is not constructible from `(d, f, λ₂)` by a fixed
  formula.
- **`C`'s exact operator form** `C = fᵀ(½diag(Ld) + ½L_W)f = ½𝒜 + N` is confirmed, but using it as a
  perturbation (`L_W f`) overshoots by `O(n³)`.

The reduced core `C + R″ ≥ 0` is therefore **not** a second-variation identity. What remains is to
exploit minimality *non-perturbatively* — e.g. via the full Courant–Fischer characterization or an
SDP/duality certificate — rather than a single explicit test vector. The degree-only inequality is
true at all scales (verified n ≤ 5000), tight on deg2+dense, but its witness is genuinely global.

## Lean
No new exact identity this round (the result is the negative variational finding). The exact pieces
used — the `C` operator/divergence form `C = ½𝒜 + N`, the degree-discrepancy energy
`N = ½Σ|d_a−d_b|(f_a−f_b)²`, and the covariance `𝒜 = dᵀL(f²)` — are already covered by the formalised
`B2prime_min_decomp`, `quadForm_weighted_laplacian` (any symmetric `W`, e.g. `W=|d_a−d_b|`), and
`degAssort_covariance`.
