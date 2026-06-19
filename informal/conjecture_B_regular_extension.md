# Conjecture B — the regular proof and its extension to irregular graphs

Correct form (cf. [`conjecture_B_edge_variance.md`](conjecture_B_edge_variance.md)):
**`B ⟺ T ≤ λ₂·G`**, `T = Σ_e t_e g_e²`, `g_e = f_a − f_b`, `h_e = f_a + f_b`,
`G = Σ_e h_e² − S²/m = m·Var_E(h)`, `Σ_e g_e² = λ₂`. Code:
[`conjecture_B_regular_extension.py`](../conjecture_B_regular_extension.py), 580 graphs.

## TASK 1 — regular case FORMALIZED in Lean (no `sorry`)

`Topostability/ConjectureB.lean` now has

> `theorem aggregate_triangle_poincare_regular (f lam d) (hreg : ∀ v, G.degree v = d)
>   (heig : (G.lapMatrix ℝ).mulVec f = lam • f) : triEnergy G f ≤ 2·lam·degQuad G f`

— the regular case of the (open) `aggregate_triangle_poincare`, fully proved. The proof is exactly
the edge-variance argument, and it does **not** need `λ₂ ≤ d+1`:

- `t_e = |N(a)∩N(b)| ≤ d − 1` (a common neighbour of an edge avoids both endpoints; proved inline
  via `N(a)∩N(b) ⊆ N(a).erase b`);
- `D := Σ_{i,j}[i∼j](f_i−f_j)² = 2·lam·‖f‖²` (Dirichlet form at the eigenvector, via
  `SimpleGraph.lapMatrix_toLinearMap₂'`);
- `triEnergy ≤ (d−1)·D` (term-wise) `≤ d·D` (since `D ≥ 0`) `= 2·lam·(d‖f‖²) = 2·lam·degQuad`
  (using `degQuad = d‖f‖²` for `d`-regular).

The factor `d/(d−1)` slack comes for free from regularity (`degQuad = d‖f‖²`); the complete graph
`K_n` is the equality case. Verified via Modal `check_file` and full build (2688 jobs, sorry-free).

## TASK 2 — irregular extension: the degree-only relaxation holds (580/580)

Replace `t_e` by its degree bound `t_e ≤ min(d_a,d_b) − 1`:

> **`B2′ := Σ_e (min(d_a,d_b) − 1)·g_e² ≤ λ₂·G`**  holds **`580/580`**,
> `B2′/(λ₂G)`: min `0.009`, median `0.689`, **max `0.926`** (7.4% margin at the tightest).

Since `t_e ≤ min(d_a,d_b) − 1`, `B2′ ≥ T`, so `B2′ ≤ λ₂G` is **stronger** than B and **eliminates the
triangle counts entirely** — the irregular proof reduces to a *degree-only* edge inequality. Hard
families are comfortable:

| family | `B2′/(λ₂G)` max |
|---|---|
| barbell | `0.500` |
| glue | `0.576` |
| chain | `0.514` |
| corpus (worst: `n=69, d_max=56, d_min=2`) | `0.926` |

This generalises the regular proof: there `min(d_a,d_b) = d` uniformly, `S = 0`, `G = 2d − λ₂`, and
`B2′ = (d−1)λ₂ ≤ λ₂(2d−λ₂)`. The irregular case keeps the per-edge weight `min−1` but now `G` carries
the `−S²/m` centering. This is the same `B2′` reduction verified earlier at scale (the open
degree-only target), here re-confirmed in the corrected `T ≤ λ₂G` form.

## TASK 3 — the average-triangle bound fails

| test | holds |
|---|---|
| `T ≤ t_avg·λ₂` (`t_avg = Σt_e/m`; Chebyshev anti-corr) | `578/580` |
| `t_avg ≤ G` | **`239/580`** |
| both (⇒ `T ≤ t_avg λ₂ ≤ λ₂G`) | `237/580` |

The Chebyshev step `T ≤ t_avg·λ₂` nearly holds (the `t`–`g²` anti-correlation), but `t_avg ≤ G`
fails on 59% of graphs (on bottlenecks `G` is small while `t_avg` is order-`d`). So the
**average** triangle count is too coarse — the *per-edge* `min(d_a,d_b)−1` weight (TASK 2) is
essential, exactly as the regular proof uses the per-edge `t_e ≤ d−1`.

## TASK 4 — relaxations and slack

| inequality | holds |
|---|---|
| `T ≤ λ₂G` (true conjecture) | `580/580` |
| `B2′ = Σ(min−1)g² ≤ λ₂G` (degree-only) | `580/580` |
| slack `Σ(min−1−t_e)g² ≥ 0` (from `t_e ≤ min−1`) | `580/580` |

The relaxation cost `(B2′−T)/(λ₂G)` has median `0.29`, max `0.72` — `B2′` discards up to 72% of the
budget yet still fits under `λ₂G`. So the triangle counts are *not* needed: the degree bound
`min−1` suffices on every tested graph.

## Conclusion

- **Regular graphs: fully proved and formalised** (`aggregate_triangle_poincare_regular`, no `sorry`),
  via `t_e ≤ d−1`, `Σg² = λ₂`, `G = 2d−λ₂`, and `D ≥ 0` — no `λ₂ ≤ d+1` needed.
- **Irregular graphs reduce to a degree-only inequality**: `Σ_e (min(d_a,d_b)−1)·g_e² ≤ λ₂·G`
  (`580/580`, max ratio `0.926`). Triangle counts are eliminated; the per-edge `min−1` weight is the
  right generalisation of the regular `d−1`.
- The **average** triangle bound (`t_avg`) is too coarse (`t_avg ≤ G` only 41%); the per-edge weight
  is essential.

The remaining open step is purely degree-spectral: prove
`Σ_e (min(d_a,d_b)−1)(f_a−f_b)² ≤ λ₂·(Σ_e (f_a+f_b)² − S²/m)` for the Fiedler `f` — no triangles, no
`Open`. For regular graphs this is the formalised theorem; the irregular case needs to handle the
`S²/m` centering against the per-edge degree minimum (the same irregular coupling, now in the
sharpest degree-only form).

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `aggregate_triangle_poincare_regular` — `triEnergy ≤ 2·lam·degQuad` for `d`-regular graphs (the
  regular case of `aggregate_triangle_poincare`). Uses the inline `t_e ≤ d−1`, the Dirichlet-form
  identity `Σ[i∼j](f_i−f_j)² = 2·lam·‖f‖²`, and `degQuad = d·‖f‖²`.
