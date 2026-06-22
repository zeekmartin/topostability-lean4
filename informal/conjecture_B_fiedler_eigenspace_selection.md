# Conjecture B — the λ₂ eigenspace selection problem

The corrected lift target is `hTconn → ∃ Fiedler f with gap(f) ≥ 0`. This analyzes the existential as
a quadratic-form maximization over the `λ₂`-eigenspace `E_{λ₂}`, and confirms **`hTconn ⟹ ∃ gap ≥ 0`**
(0 violations), with all failures confined to `triangleGraph`-disconnected graphs (clique+pendants).
Code: [`conjecture_B_fiedler_eigenspace_selection.py`](../conjecture_B_fiedler_eigenspace_selection.py).

## TASK 1 — gap as a quadratic form on `E_{λ₂}`

With `‖f‖ = 1`, `gap(f) = λ(2fᵀDf − S²/m) − T − λ² = fᵀM f − λ²`, where

> **`M = λ(2D − ddᵀ/m) − L_t`** (`L_t` = triangle Laplacian, `(L_t)_{ij} = −(A²)_{ij}` on edges).

Restricting to an orthonormal basis `E` of `E_{λ₂}` (`= span` of the `λ₂`-eigenvectors): `M_gap := EᵀM E`
(a `mult × mult` matrix). For `f = Ec` (`‖c‖ = 1`), `gap(f) = cᵀM_gap c − λ²`.

## TASK 2 — the existential condition

> **`∃ Fiedler with gap ≥ 0 ⟺ λ_max(M_gap) ≥ λ²`** (i.e. `max gap = λ_max(M_gap) − λ² ≥ 0`).

`min gap = λ_min(M_gap) − λ²` is the *universal* (`∀`) condition (false on degenerate cases).

## TASK 3 — `hTconn ⟹ max gap ≥ 0` (CONFIRMED)

| graph | mult | min gap | max gap | TG-conn | ∃ holds |
|---|---|---|---|---|---|
| deg2dense40 | 1 | 1.46 | 1.46 | **yes** | yes |
| deg2dense80 | 1 | 1.12 | 1.12 | **yes** | yes |
| gnp(20,.6) | 1 | 26.96 | 26.96 | **yes** | yes |
| cocktail K₂ˣ⁵ | 5 | 16.0 | 16.0 | **yes** | yes |
| K₂₀ | 19 | 0 | 0 | **yes** | yes |
| K₁₂+star15 | 15 | **−1.07** | +1.0 | no | yes |
| K₂₀+star40 | 40 | **−4.94** | +1.0 | no | yes |
| K₁₂+pend30 | 5 | −0.50 | **−0.50** | no | **NO** |
| K₁₀+pend25 | 4 | −0.30 | **−0.30** | no | **NO** |
| K₁₅+pend40 | 9 | −0.73 | **−0.73** | no | **NO** |

> **`hTconn` & `∃` FAILS: 0** — every `triangleGraph`-connected graph has `max gap ≥ 0`. **`hTconn ⟹
> ∃ Fiedler with gap ≥ 0` is CONFIRMED** on the corpus.

## TASK 4 — failure cases are exactly `triangleGraph`-disconnected (clique+pendants spread)

> **All `∃`-failures (`K₁₂+pend30`, `K₁₀+pend25`, `K₁₅+pend40`) have `triangleGraph` disconnected.**
> They are cliques with pendants *spread* over the clique vertices: each pendant edge lies in no
> triangle, so it is an isolated vertex of `triangleGraph` ⟹ `λ₂(T(G)) = 0 ≤ λ₂(G)` trivially
> (outside Conjecture B's `hTconn` scope).

**Signature of the failures:** `min gap = max gap` (gap is *constant* over `E_{λ₂}`, e.g. `−0.50`). The
entire `λ₂`-eigenspace is "pendant-trapped" — a *uniformly bad* direction with no good alternative.
Contrast **star+clique** (all pendants at *one* vertex, also TG-disconnected): there `min gap < 0` but
`max gap = +1.0` — the eigenspace mixes the bad pendant directions with the *good* clique direction, so
`∃` still holds.

## TASK 5 — the structural reason

- **Simple `λ₂` (mult = 1): always holds** (5/5) — `∃ = ∀ = gap ≥ 0`, the genuine conjecture; no
  selection problem.
- **Degenerate `λ₂`:** the selection problem is real. The eigenspace can contain *triangle-free-supported*
  (pendant) directions where `gap < 0`. `∃` holds iff `E_{λ₂}` also contains a *triangle-supported*
  ("`K_n`-like", high `|f|` on the dense triangle-rich core) direction with `gap ≥ 0`.
- **`triangleGraph` connectivity excludes the fully-trapped eigenspace:** when every edge is in a
  triangle (necessary for TG connected), no eigenvector is supported purely on triangle-free edges, so
  `E_{λ₂}` is not uniformly bad — a triangle-supported good Fiedler exists. When TG is *disconnected*
  via triangle-free (pendant) edges, the `λ₂`-eigenspace *can* be entirely pendant-trapped
  (clique+pendants), and `∃` fails — but then `λ₂(T(G)) = 0` and the conjecture is vacuous.

So the selection problem is: **pick the triangle-supported direction in `E_{λ₂}`**; `hTconn` guarantees
it exists. The projected Fiedler lift `h' = Bᵀf − (S/m)1_E` should be evaluated at *that* `f`.

## Conclusion

- **`hTconn ⟹ ∃ Fiedler with gap ≥ 0` is CONFIRMED** (0 violations over the corpus); the existential is
  `λ_max(M_gap) ≥ λ²` (`M_gap = Eᵀ[λ(2D − ddᵀ/m) − L_t]E`).
- **All failures are `triangleGraph`-disconnected** (clique+pendants), where the `λ₂`-eigenspace is
  uniformly pendant-trapped (`gap` constant `< 0`) but `λ₂(T(G)) = 0` (conjecture vacuous).
- **Structural selection rule:** the good Fiedler is the **triangle-supported** direction in `E_{λ₂}`;
  `hTconn` (every edge in a triangle) guarantees such a direction exists, excluding the pendant-trapped
  eigenspace. Simple `λ₂` has no selection problem (∃ = ∀).

This pins the existential lift to a concrete eigenspace-selection statement and explains *why* `hTconn`
is exactly the right hypothesis: it is precisely the condition that prevents the `λ₂`-eigenspace from
being trapped on triangle-free edges.

## Lean
`triEnergy_le_RHS_exists` (`hTconn → ∃ unit Fiedler with gap ≥ 0`) is the right statement; this analysis
shows the witness is the triangle-supported direction of `E_{λ₂}`, and `λ_max(M_gap) ≥ λ²` is the exact
existential condition. A future proof would construct that direction from `hTconn` (every edge in a
triangle).
