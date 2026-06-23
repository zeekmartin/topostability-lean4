# Conjecture B — sharpness of the `B2′ ≤ 2λ·degQuad` leaf

Analysis of the open regime-i leaf `B2′ ≤ 2λ·degQuad` (`B2prime_le_two_lam_degQuad`,
`B2′ = Σ_{i,j}[i∼j](min(d_i,d_j)−1)(f_i−f_j)²`, ordered). **Result: the extremizer is `K_n` / dense
regular (ratio `→ 1`), NOT TYPE A — the OPPOSITE of the gap conjecture. The sharp/regular case is
already PROVEN (`B2prime_le_two_lam_degQuad_regular`); the open irregular part (near-regular dense) sits
strictly below the `K_n` bound. The weighted-degree reduction `min(d_a,d_b)−1 ≤ ½(d_a+d_b)` is valid
per-edge but does NOT chain to `2λ·degQuad` via `W` (`W` is unbounded relative to the RHS on sparse
graphs).** Code: [`conjecture_B_B2prime_leaf_analysis.py`](../conjecture_B_B2prime_leaf_analysis.py).

## TASK 1/2 — ratio `B2′/(2λ·degQuad)`; extremizers

Holds **46/46**. Sharpest cases (ratio `→ 1`):

| graph | class | ratio | `1 − ratio` |
|---|---|---|---|
| `K₅₀` | REGULAR | **0.9796** | 0.020 |
| gnp(60,.7) | RANDOM | 0.9708 | 0.029 |
| `K₃₀` | REGULAR | 0.9655 | 0.034 |
| gnp(60,.5) | RANDOM | 0.9613 | 0.039 |
| `rr(40,20)` | REGULAR | 0.9500 | 0.050 |

> **`K_n` is the extremizer: ratio `= (n−2)/(n−1) → 1`** (exact: `K₁₀` 0.889, `K₂₀` 0.947, `K₅₀`
> 0.980). `B2′ = (n−2)·Dirichlet`, `2λ·degQuad = (n−1)·Dirichlet`. Dense regular and dense random
> approach the same limit.

## TASK 3/4 — by class: the hard cases are REGULAR, **not** TYPE A

| class | n | mean ratio | **max ratio** |
|---|---|---|---|
| REGULAR (incl `K_n`) | 11 | 0.892 | **0.980** |
| RANDOM (dense) | 9 | 0.923 | 0.971 |
| **TYPE A** (deg2+dense, twin-port) | 21 | 0.699 | **0.870** |
| TYPE B (lollipop, barbell) | 5 | 0.184 | 0.247 |

> **The `B2′` leaf is sharp on regular/dense and LOOSE on TYPE A — the opposite of the gap conjecture**
> (where TYPE A is the hard band `E < 0` and regular is proven). For the leaf, TYPE A has comfortable
> slack (ratio ≤ 0.87) and TYPE B is very loose (0.18); the binding direction is dense-regular.

**Consequence:** the extremizer (`K_n` / dense regular) is exactly the case **already proved sorry-free**
(`B2prime_le_two_lam_degQuad_regular`: `B2′ = (d−1)·Dirichlet ≤ d·Dirichlet = 2λ·degQuad`). The open
*irregular* part lives **strictly below** the `K_n` bound (max irregular ratio ≈ 0.97, gnp), so it is a
*perturbation* off the proven regular case — the natural proof route is interpolation from regularity,
not a fresh bound.

## TASK 5 — the weighted-degree reduction

Per-edge `min(d_a,d_b) − 1 ≤ α(d_a+d_b)`: since `min ≤ ½(d_a+d_b)`, **`α = ½` works (per-edge,
exact ceiling)**; the gradient-weighted `α_w = B2′/W ∈ [0.026, 0.490]` (`→ ½` at `K_n`). So
`B2′ ≤ ½·W` (`W = Σ_{i,j}[i∼j](d_a+d_b)(f_i−f_j)²`) always.

**But the chain `B2′ ≤ ½W ≤ 2λ·degQuad` FAILS:** it needs `W ≤ 4λ·degQuad`, and
`W/(2λ·degQuad) ∈ [0.65, 25.9]` — only **16/46** satisfy `W/RHS ≤ 2`. `W` blows up on sparse graphs
(`W/RHS = 25.9`), where `α_w` is tiny (so `B2′` stays small) but the uniform `α = ½` is far too lossy.

> **A uniform `α` cannot close the leaf.** The identity `α_w · (W/RHS) = ratio ≤ 1` holds with *both*
> factors varying wildly (`α_w` small ⟺ `W/RHS` large); the gradient weighting is essential. The `W`
> route (any constant-`α` degree bound) is ruled out — the same conclusion as the earlier `W ≤ 2λd_eff`
> failure (`conjecture_B_combinatorial_lemma.md`).

## Conclusion

- **Extremizer `K_n` (ratio `(n−2)/(n−1) → 1`); hard direction = dense-regular, NOT TYPE A** (TYPE A
  ratio ≤ 0.87, comfortable). This *inverts* the gap conjecture's regime difficulty.
- **The sharp/regular case is already PROVEN** (`B2prime_le_two_lam_degQuad_regular`); the open
  *irregular* leaf sits strictly below it (≤ 0.97), so it is a **perturbation off regularity** — the
  promising route is interpolation from the regular proof, bounding the irregular defect.
- **Weighted-degree reduction:** `α = ½` valid per-edge, but the `W`-chain fails (`W` unbounded vs RHS
  on sparse graphs); no uniform `α` works — gradient weighting is essential.

## Lean
The leaf `B2prime_le_two_lam_degQuad` remains the open regime-i sorry; its regular extremal case is
sorry-free (`B2prime_le_two_lam_degQuad_regular`). The analysis says the next step is an
*irregular-defect* bound interpolating from the regular identity `B2′ = (d−1)·Dirichlet`, not a
constant-`α` degree relaxation (ruled out).
