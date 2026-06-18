# Conjecture B — the A²-to-triangle Hadamard gap (2-path Laplacian split)

The exact Lean lemma `adjSq_mulVec_fiedler` gives `A²f = A·Df − λ₂(D−λ₂)f`, but triangle energy
uses the **Hadamard** product `M = A∘A²` (`M_ab = t_ab` on adjacent pairs), not `A²`. This note
closes the conceptual gap: it decomposes the full 2-path operator `A²` into a **closed** (triangle)
part and an **open** part, both *graph Laplacians*, and shows the triangle energy equals the full
`A²` eigen-recursion **minus a manifestly nonnegative open-2-path remainder**.
Code: [`conjecture_B_A2_triangle_gap.py`](../conjecture_B_A2_triangle_gap.py).

---

## 1. The 2-path operator splits into closed + open (both Laplacians)

Entrywise `(A²)_{ab} = #\{c : a∼c∼b\}` = common neighbours. Split every 2-path `a−c−b` by whether
its endpoints are adjacent:

> **`A² = diag(d) + M + P`**  (residual `0`, exact),
> `M_ab = t_ab·[a∼b]` (**closed** 2-paths = triangle edges),  `P_ab = (A²)_{ab}·[a≁b, a≠b]`
> (**open** 2-paths),  `diag(d)` the `a=c=b`-return walks.

Let `σ_v = Σ_{c∼v} d_c = (A d)_v` (sum of neighbour degrees). The **2-path graph** (pair `(a,b)`
weighted by common-neighbour count) has Laplacian `L₂ = diag(σ) − A²`, and it splits exactly into
the **triangle Laplacian** and the **open-2-path Laplacian**:

> **`L₂ = L_M + L_P`**  (residual `0`),
> `L_M = diag(τ) − M`  (`τ_v = Σ_{u∼v} t_{vu}`),  `L_P = diag(σ−d−τ) − P`.

Both `L_M, L_P` are genuine graph Laplacians, hence **PSD** (verified: `λ_min(L_P) ≈ 0`). So

> `T = fᵀL_M f = Σ_{ab∈E} t_ab(f_a−f_b)² ≥ 0`,   `Open = fᵀL_P f = Σ_{a≁b} (A²)_{ab}(f_a−f_b)²/2 ≥ 0`.

## 2. The full A² recursion is a sum of apex squares (eigen)

`A²` is governed by the eigen-equation through a **sum of squares over apices**. With
`s_c = (Af)_c = Σ_{a∈N(c)} f_a`:

> **`fᵀA²f = Σ_c s_c² = Σ_c (Σ_{a∈N(c)} f_a)²`**  (apex sum; this is the `quadForm_adjSq` lemma),
> and `Af = (D−λ₂)f` ⇒ `s_c = (d_c−λ₂)f_c`, so **`fᵀA²f = Σ_v (d_v−λ₂)² f_v²`** (residual `6·10⁻¹²`).

This is the requested apex-sum view: the full 2-path form is a positive combination of squared
neighbourhood sums, each pinned by the eigenvalue. It controls **both** the closed and open parts
at once.

## 3. The exact nonnegative-remainder identity

Combining §1–§2 (`fᵀL₂f = Σσ_v f_v² − fᵀA²f`):

> **`T + Open = Σ_v [σ_v − (d_v − λ₂)²] f_v²`**,   `T, Open ≥ 0`.   (residual `6·10⁻¹²`, **exact**)

Reading it as an upper bound on the triangle energy:

> **`T = Σ_v [σ_v − (d_v−λ₂)²] f_v²  −  Open`**,   `Open ≥ 0`.

So the **closed** (triangle) contribution is exactly the full-`A²` eigen-recursion diagonal
`Σ[σ_v−(d_v−λ₂)²]f_v²` **minus** the nonnegative open-2-path energy. Equality (`Open = 0`) holds
iff every neighbourhood `N(c)` is a clique — i.e. locally chordal/clique structure; the open
remainder measures exactly the failure of neighbourhoods to be complete.

### Why this is the right "control"

The apex sum `Σ_c s_c²` is a sum of squares fixed by the eigen-equation, with **no sign or
cancellation problems** — unlike the edge-local triangle correlation `fᵀM f`, which is sign-
indefinite (the original obstruction). The Hadamard gap `A² → M` is precisely `diag(d) + P`: the
return-walk diagonal (trivial) plus the open-2-path Laplacian `L_P` (nonnegative). The triangle
energy is thus never *more* than the controllable recursion diagonal.

## 4. Equivalent reformulation of the aggregate Poincaré (open-energy lower bound)

Substituting the exact identity into the target `T ≤ λ₂·Σ_v d_v f_v²`:

> **aggregate Poincaré ⟺ `Open ≥ Σ_v [σ_v − (d_v−λ₂)² − λ₂ d_v] f_v²`.**

Verified `580/580` (slack `= −Q ≥ 0`, min `0.087`). This **converts an upper bound on the triangle
energy into a lower bound on the open-2-path Laplacian energy** `Open = fᵀL_P f` — a single global
sum of squares, not an edge-local or per-apex statement. For a `d`-regular graph the right side is
`λ₂(d−λ₂)·Σf_v²` and the statement reads `fᵀL_P f ≥ λ₂(d−λ₂)`: the open-2-path energy must clear a
multiple of the spectral gap.

## 5. Status

- **Exact, verified (580 graphs):** the splittings `A² = diag(d)+M+P`, `L₂ = L_M+L_P`; the apex
  sum-of-squares `fᵀA²f = Σ_c s_c² = Σ_v(d_v−λ₂)²f_v²`; and the master remainder identity
  `T + Open = Σ_v[σ_v−(d_v−λ₂)²]f_v²`.
- **Formalised (Lean, `ConjectureB.lean`, no `sorry`):**
  - `adjMatrix_mulVec_fiedler` — `A f = D f − λ f`;
  - `adjSq_mulVec_fiedler` — `A²f = A·Df − λ(D f − λ f)`;
  - `quadForm_adjSq_eq_normSq` — `fᵀA²f = Σ_v ((Af)_v)²` (the apex sum-of-squares, symmetry only).
- **Open:** the open-energy lower bound `fᵀL_P f ≥ Σ_v[σ_v−(d_v−λ₂)²−λ₂d_v]f_v²`. Both sides are
  now nonnegative quadratic forms in `f` (the LHS a graph-Laplacian Dirichlet energy), with the
  eigenvalue entering only through the diagonal coefficient — no per-edge positivity, no per-apex
  Rayleigh, no hub-flatness.

**Next lever (not a closed route):** lower-bound the open-2-path Dirichlet energy `fᵀL_P f`
spectrally. `L_P` is a PSD graph Laplacian on the open-2-path graph; the target diagonal
`σ_v−(d_v−λ₂)²−λ₂d_v` is what its Dirichlet energy on the *specific* Fiedler vector must exceed.
This keeps the problem aggregate and sign-free, where the previous edge-local routes failed.
