# Conjecture B — eigenspace-selection lemma: proof skeleton

**Target.** If `triangleGraph T(G)` is connected, then `∃ f ∈ E_{λ₂}, ‖f‖=1, f⊥1, gap(f) ≥ 0`. This
analysis reduces the *existential* (over the eigenspace) to a single **trace** inequality, confirms it
under `hTconn` (10/10), characterizes the witness, and tests the `T(G)`-Fiedler correspondence. Code:
[`conjecture_B_eigenspace_selection_proof.py`](../conjecture_B_eigenspace_selection_proof.py).

## TASK 1 — gap on `E_{λ₂}`

`gap(f) = fᵀM f − λ²` (`‖f‖=1`), `M = λ(2D − ddᵀ/m) − L_t` (`L_t` = triangle Laplacian). Restriction
to an orthonormal eigenbasis `E` of `E_{λ₂}`: `M_gap = EᵀM E` (`mult × mult`).

## TASK 2 — the bad subspace

`Bad = {f ∈ E_{λ₂} : gap(f) < 0}` = the negative cone of `M_gap − λ²I`. The existential is
`Bad ≠ E_{λ₂}`, i.e. `λ_max(M_gap) ≥ λ²`. **Bad = E_{λ₂}** (total failure) ⟺ `M_gap ≺ λ²I` ⟺ gap
*uniformly* negative — observed only on the pendant-trapped (TG-disconnected) families.

## TASK 3 — the TRACE route (the key simplification)

`λ_max(M_gap) ≥ avg eigenvalue = trace(M_gap)/mult`. So a **sufficient** condition for the existential:

> **`trace(M_gap) ≥ mult·λ²`** (equivalently `avg gap = trace(M_gap)/mult − λ² ≥ 0`)
> `⟹ λ_max(M_gap) ≥ λ² ⟹ ∃ f with gap(f) ≥ 0`.

`trace(M_gap) = Σ_k gap(φ_k) + mult·λ²` over *any* orthonormal eigenbasis (basis-independent), so the
trace condition is `Σ_k gap(φ_k) ≥ 0`. **Verified: `avg gap ≥ 0` on 10/10 `triangleGraph`-connected
graphs** (incl. degenerate `K₁₂` mult 11, `K₂₀` mult 19, cocktail mult 5, `K_{3,3,3}` mult 6, wheel,
octahedron, and simple-`λ₂` deg2+dense, gnp, rr). The pendant-trapped failures (`K₁₂+pend30`, TG-disc)
have `avg = min = max < 0`.

> **The trace route DISSOLVES the degeneracy/selection problem:** `∃ f` over the eigenspace reduces to a
> *single scalar* inequality `trace(M_gap) ≥ mult·λ²`, basis-independent, no eigenvector search.

**Honest scope.** For **simple `λ₂`** (mult = 1) the trace condition *is* `gap ≥ 0` — the core
conjecture, not made easier. So the trace route does not bypass the underlying inequality; it shows that
**degeneracy adds no difficulty beyond the average** — the selection lemma is exactly as hard as the
simple-`λ₂` bound, no harder. (`trace = Σ_k gap(φ_k)`; the average over the eigenbasis is what must be
`≥ 0`.)

## TASK 4 — the constructive witness

The witness is the **top eigenvector of `M_gap`** (largest `λ_max(M_gap)`), lifted to `E_{λ₂}` via
`f = E c` (`c` = top eigenvector of `M_gap`). It maximizes `gap` over the eigenspace; `gap(witness) =
λ_max(M_gap) − λ² = max gap ≥ 0` under `hTconn`.

## TASK 5 — does the witness correspond to a `T(G)` Fiedler / lift?

Witness lift `= Bᵀf` (gradient `g_e = f_a − f_b`, centered) — a vector on `V(T(G)) = E(G)`:

| graph | `|cos(lift, T(G)-Fiedler)|` | `Ray_{T(G)}(lift)` | `λ₂(T(G))` | `λ₂(G)` |
|---|---|---|---|---|
| **deg2dense40** | **0.975** | 1.56 | 0.94 | 1.97 |
| **deg2dense60** | **0.985** | 1.58 | 0.96 | 1.98 |
| gnp(20,.6) | 0.50 | 5.97 | 1.61 | 5.32 |
| `K₁₂` (degenerate) | 0.43 | 18.0 | 12.0 | 12.0 |
| cocktail (degenerate) | 0.09 | 12.9 | 6.0 | 8.0 |

> **For the genuine simple-`λ₂` bottleneck (deg2+dense), the witness gradient ≈ the `T(G)` Fiedler**
> (`|cos| ≈ 0.97–0.99`): the eigenspace witness *is* essentially the optimal `T(G)` test vector — a
> clean duality. For *degenerate dense* graphs the correspondence is weak (`|cos|` low) because the
> centered gradient is not the correctly-normalized projected lift `h' = Bᵀf − (S/m)1_E`; there
> `λ₂(T(G)) ≤ λ₂(G)` holds via a different vector (and equality at `K_n`).

## Proof skeleton

1. **Reduce existential to trace:** `∃ f, gap(f) ≥ 0 ⟸ trace(M_gap) ≥ mult·λ²` (avg ≥ max-dominates).
2. **Trace identity:** `trace(M_gap) = λ(2·tr(P_E D) − mult·λ − (1/m)Σ_k (dᵀφ_k)²) − Σ_k T(φ_k)`
   (`P_E` = projection onto `E_{λ₂}`; `φ_k` orthonormal eigenbasis). The open content is the trace
   bound `Σ_k T(φ_k) ≤ λ(2 tr(P_E D) − mult λ − (1/m)Σ_k(dᵀφ_k)²)`.
3. **`hTconn` role:** every edge is in a triangle ⟹ no eigenvector of `E_{λ₂}` is supported purely on
   triangle-free edges ⟹ the eigenspace is not pendant-trapped ⟹ trace `≥ 0` (excludes `Bad = E_{λ₂}`).
4. **Witness:** top eigenvector of `M_gap`; for the bottleneck case it is the `T(G)`-Fiedler lift.

## Honest status

- **Cannot prove the lemma outright** — for simple `λ₂` it *is* the open conjecture `gap ≥ 0`. But:
- **Degeneracy is dissolved:** the selection over `E_{λ₂}` reduces to the basis-independent trace
  inequality `trace(M_gap) ≥ mult·λ²` (avg gap ≥ 0), verified 10/10 under `hTconn`. So the existential is
  *no harder* than the simple-`λ₂` bound.
- **Witness identified** (top `M_gap` eigenvector); for the bottleneck it is the `T(G)` Fiedler lift.

## Lean target

> `triEnergy_le_RHS_exists` (`hTconn → ∃ unit Fiedler, gap ≥ 0`) ⟸ `trace_Mgap_ge` :
> `trace(M_gap) ≥ mult·λ²`. The trace route is the formalization-friendly reduction (a single scalar
> inequality, no eigenvector existential). For mult = 1 it is the simple-`λ₂` bound `gap ≥ 0`
> (= `triEnergy_le_RHS_regular` already covers regular; general simple-`λ₂` is the standing open core).
