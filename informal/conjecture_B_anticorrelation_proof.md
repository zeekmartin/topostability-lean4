# Conjecture B — the universal anti-correlation `Cov(t_e, g_e²) ≤ 0`

Try to prove `Cov(t_e, g_e²) ≤ 0` (uniform measure over edges), i.e. `m·Σ_e t_e g_e² ≤ (Σ_e t_e)(Σ_e
g_e²)` — the Fiedler-weighted average of triangle counts is `≤` the uniform average. **Result: the
inequality is ROBUSTLY UNIVERSAL (62/62, including adversarial triangle-rich-cut constructions; strictly
negative on asymmetric graphs, `= 0` only on symmetric/regular). The mechanism is self-reinforcing
(triangle-rich = dense = high-connectivity = FLAT, so low `g²`). BUT it resists proof: it is a
Chebyshev-type inequality with NO total ordering of `t` and `g²`; the SBP/apex/variational routes restate
it but do not close it. And (from the covariance round) it is INSUFFICIENT for the aggregate anyway — the
magnitude, not just the sign, is needed.** Code:
[`conjecture_B_anticorrelation_proof.py`](../conjecture_B_anticorrelation_proof.py).

## TASK 5 — universality (robust, including adversarial)

| corpus | `Cov ≤ 0` |
|---|---|
| standard (regular, multipartite, gnp, deg2+dense, twin) | all |
| **two cliques + bridge fully joined (triangle-rich cut)** | all (`= 0` symmetric) |
| **clique-path / dense-bridge barbell** | all |
| **asymmetric: path–clique–path, unequal cliques, clique+tail, barbell+clique-bridge** | all, **strict `< 0`** (max `−2·10⁻⁴`) |
| **TOTAL** | **62/62** |

> **No counterexample.** Even when the bottleneck is deliberately triangle-rich, the Fiedler stays *flat*
> there: a triangle-dense region is high-connectivity, which pulls its vertices toward a common value
> (`Σ_{u∼v}f_u = (d_v−λ)f_v` forces high-degree vertices near the local mean). So high-`t` edges keep low
> `g²` — the anti-correlation is **self-reinforcing** and cannot be broken by a triangle-rich cut.

## TASK 1 — apex form (restates, doesn't close)

`T = Σ_c E_{G[N(c)]}`, `Σ_c|E_c| = 3·num_tri = Σ_e t_e`, `λ = Σ_e g²`. The inequality becomes
`Σ_c|E_c|·(avg_{N(c)} g² − global avg g²) ≤ 0` — neighbourhoods with more edges (more triangles) carry
below-average `g²`. This is the anti-correlation *at the apex level*, not a proof; the per-apex form
`E_c ≤ 2λ|E_c|/m` is a *local normalized Poincaré* that fails per-apex (only the aggregate holds, by
compensation).

## TASK 3 — SBP route (wrong weighting)

The SBP identity `Σ_{a∼b}(σ_a+σ_b)f_af_b = Σ_v σ_v(d_v−λ)f_v²` (`σ_v` = triangle degree) connects
`σ`-*weighted* edge products to `σ(d−λ)f²`. But the target `m·Σ t_e g² ≤ λ·Σσ_v/...` involves the
*Hadamard* `t_e g²` (per-edge triangle count × gradient), which `Lf = λf` does not reach (the triangle
energy `T = fᵀL_t f` is Hadamard `A²⊙A`, not a polynomial in `A` — see
`conjecture_B_matrix_power_route.md`). So SBP gives the wrong object.

## TASK 4 — Chebyshev (no total order)

`Cov ≤ 0 ⟺ m·Σ t_e g² ≤ (Σ t_e)(Σ g²)` is exactly **Chebyshev's sum inequality** for *oppositely sorted*
sequences. But `t_e` and `g_e²` have **no total order** — the Fiedler induces only a partial,
graph-dependent ordering (high `g²` on cut edges, high `t` in the interior). There is no classical
Chebyshev/rearrangement that applies; a "graph-Chebyshev" would have to encode the spectral fact that the
interior (high `t`) is flat — which is the content itself. (FKG/correlation inequalities need a lattice
structure not present here.)

## Why it's true but unprovable-by-these-routes

The anti-correlation is the *spectral* fact "the Fiedler is flat on dense subgraphs" (`λ₂` localizes its
variation on sparse cuts). It is robustly true (62/62) but:
- **not algebraic** (`Lf = λf` reaches only `fᵀA²f = Σ(d−λ)²f²`; the Hadamard `t_e g²` is out of reach);
- **not a sorting inequality** (no total order on edges);
- **not local** (per-apex fails; only the aggregate holds).
It is the same difficulty class as the aggregate — a *qualitative* spectral Poincaré.

## Insufficiency (recap)

Even a proof of `Cov ≤ 0` would **not** close the aggregate: `E_μ[t] = t_bar + m·Cov/λ ≤ t_bar`, but
`t_bar ≤ d_eff` FAILS on bottlenecks (`t_bar/d_eff` up to 19.8, `conjecture_B_covariance_route.md`). The
aggregate needs the *magnitude* `Cov ≤ (λ/m)(d_eff − t_bar)` (very negative on bottlenecks), not just the
sign.

## Conclusion

- **`Cov(t_e, g_e²) ≤ 0` is robustly universal** (62/62 incl. adversarial triangle-rich cuts; strict on
  asymmetric, `= 0` symmetric). Mechanism: triangle-rich = dense = flat (self-reinforcing).
- **No proof via apex / SBP / Chebyshev** — Hadamard (not polynomial), no total order, not local. Same
  difficulty as the aggregate (qualitative).
- **Insufficient anyway** — the aggregate needs the magnitude, not the sign.

## Lean
No code change: `Cov ≤ 0` is a hard spectral conjecture (Hadamard, no sorting) and is insufficient for
the aggregate (magnitude needed). `aggregate_triangle_poincare` stays the direct sorry; the genuinely
sufficient form remains the eigenspace-PSD `λD − L_t ⪰ 0 on E_{λ₂}`. 3 sorrys unchanged.
