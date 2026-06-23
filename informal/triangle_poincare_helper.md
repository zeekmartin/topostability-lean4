# Conjecture B — the degree-edge helper and why it does NOT reduce the aggregate

Target: per-mode triangle Poincaré `Σ_e t_e(u_a−u_b)² ≤ λ·Σ_v d_v u_v²` for `Lu = λu`. **Result: the
requested helper `Σ_{i∼j}(d_i+d_j)u_iu_j = Σd²u² − λ·degQuad` is an exact, clean, eigenvector identity
(provable in two lines). BUT it concerns the *degree-edge* term, which does NOT appear in the target —
the target is purely the *triangle* term `Σ_e t_e g² = uᵀ(A²⊙A)u` (Hadamard `A∘A²`, not a polynomial in
`A`). So the helper does not reduce `aggregate_triangle_poincare`; the aggregate is already its own
smallest (triangle) form. A Lean formalization of the helper was attempted but hit rewrite-API friction
and was reverted (it is orthogonal to the aggregate anyway); the build stays green at 3 sorrys.**

## TASK 1 — the helper (exact, clean proof)

> **`Σ_{i∼j}(d_i+d_j)u_iu_j = Σ_v d_v²u_v² − λ·degQuad`** for any Laplacian eigenpair `(λ,u)`.

Matrix proof: `Σ_{i∼j}(d_i+d_j)u_iu_j = uᵀA(Du)` (`A=adjMatrix`, `D=degMatrix`; each edge contributes
`d_i u_iu_j + d_j u_iu_j`). Since `A` is symmetric, `uᵀA(Du) = (Au)ᵀ(Du)`, and `Au = (D−λ)u`
(`adjMatrix_mulVec_fiedler`), so
`uᵀA(Du) = ((D−λ)u)ᵀ(Du) = (Du)ᵀ(Du) − λ·uᵀ(Du) = Σd_v²u_v² − λ·degQuad`. ∎
(Verified to machine precision in all prior rounds — it is the same identity used in the `S`-matrix
decomposition, `slack_matrix_vertex_edge_decomposition.md`.)

## TASK 2 — the target's cleanest equivalent

Triangle expansion: `T = Σ_e t_e(u_a−u_b)² = Σ_v σ_v u_v² − uᵀ(A²⊙A)u` (`σ_v = Σ_{u∼v}t_{vu}`,
`A²⊙A` = `A²` masked to edges). So

> **target `T ≤ λ·degQuad ⟺ uᵀ(A²⊙A)u ≥ Σ_v(σ_v − λ d_v)u_v²`** (`uᵀ(A²⊙A)u = 2Σ_e t_e u_au_b`).

**The helper does not appear here.** The degree-edge term `Σ_{i∼j}(d_i+d_j)u_iu_j` is a *different*
quantity (it is `uᵀ(½(AD+DA))u`-related); the target involves the *triangle* Hadamard term `uᵀ(A²⊙A)u`.
The helper closes the degree-edge term but the triangle term is untouched.

## TASK 3 — proof via `Lu=λu` + SBP: FAILS at the triangle term

The eigenvector equation `Au = (D−λ)u` (and `A²u = A(Du) − λ(Du−λu)`, `adjSq_mulVec_fiedler`) reaches
*polynomials in `A`*: `uᵀA u = degQuad − λ`, `uᵀA²u = Σ(d_v−λ)²u_v²`, and the degree-edge helper above.
But the triangle term is `uᵀ(A²⊙A)u` — the **Hadamard** product `A∘A²`, which is **not a polynomial in
`A`** (`conjecture_B_matrix_power_route.md`: best linear fit to `{uᵀA²u, uᵀA³u, Σdᵏu²}` has residual
0.12; `uᵀA³u` is already an edge sum, not reducible). So summation-by-parts / the eigenvector recursion
**cannot reach the triangle term** — exactly the Hadamard obstruction. No SOS / SBP proof.

## TASK 4 — Lean: the helper does not reduce the aggregate

`aggregate_triangle_poincare` is `triEnergy ≤ 2λ·degQuad`, i.e. `T ≤ λ·degQuad` — *already* the pure
triangle term (`triEnergy = 2·uᵀL_t u = 2·Σ_e t_e g²`). The degree-edge helper concerns a different
term that does not occur in this statement, so formalizing it would **not** shrink the sorry. (The
helper *was* used, and cancels, in the `S = ½(LD+DL) − L_t` decomposition — but that decomposition is
circular, returning `Slack = λ·degQuad − T`.)

A Lean formalization `degEdge_eigen` (`uᵀA(Du) = (Du)·(Du) − λ·uᵀDu`, via `adjMatrix_mulVec_fiedler`
+ `dotProduct_mulVec` + `transpose_adjMatrix`) was attempted but hit `rw`-targeting friction in the
matrix-API; since it is orthogonal to the aggregate it was reverted to keep the build green. The
aggregate stays the direct sorry on its smallest (triangle) form.

## Conclusion

- **Helper (TASK 1):** `Σ_{i∼j}(d_i+d_j)u_iu_j = Σd²u² − λ·degQuad` — exact, clean (`Au=(D−λ)u`).
- **But orthogonal (TASK 2/4):** the target is the *triangle* term `uᵀ(A²⊙A)u`, not the degree-edge
  term; the helper does not appear in / reduce `aggregate_triangle_poincare`.
- **No SBP proof (TASK 3):** the eigenvector equation reaches only polynomials in `A`; the triangle term
  is the Hadamard `A∘A²`, not a polynomial — the irreducible obstruction.
- **Lean:** aggregate is already the smallest triangle form; the helper is orthogonal (formalization
  attempted, reverted; build green, 3 sorrys).

## Lean
No net code change (helper reverted — orthogonal to the aggregate). `aggregate_triangle_poincare` stays
the direct sorry (`triEnergy ≤ 2λ·degQuad`, the pure triangle term). The degree-edge helper is a clean
true identity but does not touch the Hadamard triangle term that is the aggregate's content. 3 sorrys
unchanged.
