# Conjecture B — the signless-Laplacian route for `B2′ ≤ λ₂G`

Target: `fᵀL_w f ≤ λ₂(fᵀQ f − S²/m)`, `L_w` = weighted Laplacian (`w_e = min(d_a,d_b)−1`),
`Q = D+A` signless Laplacian, `f` = Fiedler (`Lf = λ₂f`), `S = Σ d_v f_v`. **Verdict: the scalar /
eigenvalue forms of this route (Cauchy–Schwarz, `fᵀQf ≥ q₂`) FAIL on the hard family (deg2+dense); the
genuine content is the *operator* inequality, not reducible to coarse spectral bounds.** Code:
[`conjecture_B_signless_laplacian.py`](../conjecture_B_signless_laplacian.py).

## TASK 1 — operator form; regular case

Target as operator inequality on the Fiedler space: `L_w ⪯ λ₂(Q − (S²/m)·P)` (`P` the projector
removing the `S`-deficit). **Regular `d`-graph:** `L_w = (d−1)L` and `Q = (d+1)I` on `1⊥`, so
`fᵀL_w f = (d−1)λ₂`, `fᵀQf − S²/m = 2d − λ₂`, and the inequality is `(d−1)λ₂ ≤ λ₂(2d−λ₂) ⟺ λ₂ ≤ d+1` —
true (verified). **Irregular:** `L_w` and `Q` no longer co-diagonalize on `f`; the relationship is the
open content. `B2′ ≤ λ₂G` itself holds 27/27 on the corpus.

## TASK 2 — `L_w` decomposition (already formalised)

`w_e = min(d_a,d_b) − 1 = ½(d_a+d_b) − ½|d_a−d_b| − 1`, so

> `L_w = ½·L_{(d_a+d_b)} − ½·L_{|d_a−d_b|} − L`,

where `L_{(d_a+d_b)}` has edge weights `d_a+d_b` and `L_{|d_a−d_b|}` weights `|d_a−d_b|`. This is exactly
`B2prime_min_decomp` (Lean, sorry-free). `L_{(d_a+d_b)}` is the degree-weighted Dirichlet form (the
`½𝒜 + N` assortativity split, prior rounds); it is *not* `Q` directly — `Q`'s quadratic form is
`fᵀQf = Σ_e (f_a+f_b)²` (the `h`-energy), a *different* object from `L_{(d_a+d_b)}`'s `Σ_e(d_a+d_b)(f_a−f_b)²`.

## TASK 3 — the Cauchy–Schwarz / scalar route FAILS

`fᵀL_w f = Σ_e (min(d_a,d_b)−1)(f_a−f_b)²` is a reweighting of `Σ_e(f_a−f_b)² = λ₂`. Cauchy–Schwarz
gives the **valid** but **lossy** bound `fᵀL_w f ≤ w_max·λ₂ = (Δ−1)λ₂` (holds 27/27). Closing the
target this way needs `Δ−1 ≤ fᵀQf − S²/m`:

> **`(Δ−1) ≤ fᵀQf − S²/m` holds only 9/27** — it **fails** precisely on the hard family:

| graph | `Δ−1` | `fᵀQf − S²/m` | `(Δ−1)/Gvar` |
|---|---|---|---|
| K₂₀ | 18 | 18.0 | 1.0 (tight) |
| deg2+dense(40) | 30 | 2.34 | **12.8** |
| deg2+dense(80) | 59 | 2.15 | **27.5** |

**`w_max = Δ−1 = O(n)` but `fᵀQf − S²/m = O(1)`** on deg2+dense (one high-degree-incident edge inflates
`w_max`, but the bottleneck makes `Gvar` small). The max-weight Cauchy–Schwarz is off by `Θ(n)` — the
scalar route is hopeless on the bottleneck family. (Only the complete graph saturates it, `Δ−1 = Gvar`.)

## TASK 4 — signless eigenvalue connection FAILS too

`fᵀQf = Σ_k q_k|⟨f,φ_k^Q⟩|²`. A bound `fᵀQf ≥ q₂` (second-smallest `Q`-eigenvalue) would need `f` to
avoid `Q`'s lowest mode. **It holds 25/27 but FAILS on deg2+dense:**

| graph | `fᵀQf` | `q_min` | `q₂` | `fᵀQf ≥ q₂`? |
|---|---|---|---|---|
| typical gnp/rr | … | … | … | yes |
| deg2+dense(40) | **3.43** | 1.89 | **15.92** | **NO** |
| deg2+dense(80) | **3.32** | 1.96 | **39.40** | **NO** |

> The `L`-Fiedler `f` is **strongly aligned with `Q`'s *lowest* mode** on the bottleneck family
> (`fᵀQf ≈ q_min ≈ 2`, far below `q₂`). Only `fᵀQf ≥ q_min` holds universally (Rayleigh, 27/27) — too
> weak. So the signless spectrum gives no usable lower bound on `fᵀQf` exactly where it is needed.

## TASK 5 — literature

The relevant known result is a **moment inequality** for weighted-Laplacian eigenvalues:

- **Agbanusi–Bronski–Kielty, *A moment inequality and positivity for signed graph Laplacians*** (arXiv
  [2005.09608](https://arxiv.org/abs/2005.09608)): bounds weighted-Laplacian eigenvalues via the first
  two **moments of the edge weights**, the equally-weighted Laplacian eigenvalues, and the **line-graph
  adjacency** spectrum. This is the closest framework to `L_w` vs `L`, but it bounds *eigenvalues of
  `L_w`*, not the *Fiedler-vector quadratic form* `fᵀL_w f` against `fᵀQf` — and it routes through the
  line graph, which (like our CS bound) is too coarse for the bottleneck.
- Largest-Laplacian-eigenvalue bounds for weighted graphs ([Hindawi 2013](https://www.hindawi.com/journals/ijcom/2013/520610/));
  `Σ` Laplacian-eigenvalues vs `Σ` degrees ([arXiv 2508.04209](https://arxiv.org/pdf/2508.04209));
  signless-Laplacian least eigenvalue & max degree ([PMC5440539](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC5440539/));
  de Abreu's survey ([algebraic connectivity](https://www.math.ucdavis.edu/~saito/data/graphlap/deabreu-algconn.pdf)).

**No result bounds `fᵀL_w f` (min-degree-weighted Dirichlet energy at the Fiedler) by
`λ₂·(fᵀQf − S²/m)`.** The min-degree weighting and the *specific* test vector `f` (the `L`-Fiedler, not
a `Q`/`L_w`-eigenvector) put this outside the known weighted/signless-Laplacian eigenvalue inequalities.

## Conclusion

- **The signless-Laplacian route, in its scalar/eigenvalue forms, FAILS** on the bottleneck family:
  Cauchy–Schwarz (`w_max·λ₂`) is off by `Θ(n)` (`Δ−1 = O(n) ≫ fᵀQf − S²/m = O(1)`), and `fᵀQf ≥ q₂`
  fails (the Fiedler hugs `Q`'s lowest mode, `fᵀQf ≈ q_min`).
- **`L_w` decomposition** (`= ½L_{d_a+d_b} − ½L_{|Δd|} − L`) is exact (`B2prime_min_decomp`), but
  `L_{d_a+d_b} ≠ Q` (different quadratic forms), so it does not reduce `B2′ ≤ λ₂G` to a clean
  `L_w ⪯ cQ` operator bound.
- **The genuine target is the operator inequality** `L_w ⪯ λ₂(Q − (S²/m)P)` on `1⊥`, which is *not*
  implied by any scalar weight bound or `Q`-eigenvalue bound — consistent with the standing finding
  that the obstruction is a fine spectral balance (the `gap = R″ + C` near-cancellation), not a coarse
  inequality. The literature (moment / line-graph bounds) does not reach it.

This closes the signless-Laplacian route as another *coarse-bound* approach that fails on the
deg2+dense bottleneck — the same wall as the S-procedure, curvature, and resultant routes. The
remaining viable path stays the TYPE A extremality program (`gap/eff ≥ 1/3`,
`CONJECTURE_B_STATUS.md` §10).

## Lean
No new lemma (negative result). `B2prime_min_decomp` (the `L_w` split) and `quadForm_weighted_laplacian`
are already sorry-free; the regular case `λ₂ ≤ d+1` is captured by `aggregate_triangle_poincare_regular`.

Sources:
- [A moment inequality and positivity for signed graph Laplacians (arXiv 2005.09608)](https://arxiv.org/abs/2005.09608)
- [Bounds for the Largest Laplacian Eigenvalue of Weighted Graphs (Hindawi 2013)](https://www.hindawi.com/journals/ijcom/2013/520610/)
- [Sums of Laplacian eigenvalues and sums of degrees (arXiv 2508.04209)](https://arxiv.org/pdf/2508.04209)
- [Least signless Laplacian eigenvalue, fixed maximum degree (PMC5440539)](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC5440539/)
- [Old and new results on algebraic connectivity (de Abreu)](https://www.math.ucdavis.edu/~saito/data/graphlap/deabreu-algconn.pdf)
