# Conjecture B — exact nodal decomposition of the aggregate triangle-Poincaré

Target (open `aggregate_triangle_poincare`): for a unit Fiedler vector `f` (`L_G f = λ₂ f`),
`T ≤ λ₂·fᵀDf` where `T = Σ_{ab∈E} t_ab(f_a−f_b)²`, `t_ab = |N(a)∩N(b)|`, `fᵀDf = Σ_v d_v f_v²`.
(Ordered Lean form `triEnergy ≤ 2λ₂·degQuad` carries an overall factor 2.)

The per-edge route is dead (per-edge positivity false; hub-flatness ~120× too loose — see
[`conjecture_B_nodal_hard_edges.md`](conjecture_B_nodal_hard_edges.md)). This note finds the
**exact global identity** the previous note asked for: one in which the negative reservoir
appears as a single global sum, not edge-by-edge.
Code: [`conjecture_B_nodal_decomposition.py`](../conjecture_B_nodal_decomposition.py).

---

## The master identity (exact, no eigen-equation needed)

Expand the square `(f_a−f_b)² = f_a²+f_b²−2f_a f_b` inside `T` and collect the diagonal:

> **`T = Σ_v τ_v f_v² − 2·Σ_{ab∈E} t_ab f_a f_b`**,  where `τ_v := Σ_{u∼v} t_{uv}` (= twice the
> number of triangles through `v`).

Subtract `λ₂·fᵀDf = λ₂·Σ_v d_v f_v²` (just a scalar multiple of a diagonal sum):

> **`T − λ₂·fᵀDf = Δ − C`**,
> `Δ := Σ_v (τ_v − λ₂ d_v) f_v²`  ("diagonal"),  `C := 2·Σ_{ab∈E} t_ab f_a f_b` ("correlation").

Both forms are **purely algebraic** — they need no spectral hypothesis (`λ₂` enters only as the
scalar weighting `fᵀDf`). Numerically exact to machine precision on all 560 graphs
(`|Q−(Δ−C)|` max `8·10⁻¹¹`, median `3·10⁻¹⁵`).

## The nodal split of the correlation — where the reservoir lives

Split edges by nodal class `V+ = {f≥0}`, `V- = {f<0}`. Since `t_ab ≥ 0`:

> **`C = C_same − C_hard`**,
> `C_same = 2·Σ_{same-sign edges} t_ab|f_a f_b| ≥ 0`  (global same-sign triangle correlation),
> `C_hard = 2·Σ_{cross-sign edges}  t_ab|f_a f_b| ≥ 0`  (the hard nodal-boundary mass).

Hence the **exact reduction**

> **`T − λ₂·fᵀDf = Δ + C_hard − C_same`**,  so  `aggregate_triangle_poincaré ⟺ Δ + C_hard ≤ C_same`.

The negative reservoir is now a **single global sum** `C_same` — the same-sign triangle
correlation over the whole graph — exactly as required. The obstruction is the diagonal `Δ`
plus the global hard mass `C_hard`. (`|Q−(Δ+C_hard−C_same)|` max `8·10⁻¹¹` across the corpus.)

## What the numerics say (560 graphs incl. bottleneck families)

| fact | value |
|---|---|
| `Q ≤ 0` holds | **560/560** |
| reduction `Δ + C_hard ≤ C_same` holds | **560/560** |
| `(Δ+C_hard)/C_same`: median / mean / **max** | 0.48 / 0.11 / **0.9999** |
| `Δ/C_same`: min / median / max | −20.9 / 0.42 / 0.9999 |
| `Δ ≤ 0` (diagonal sign) | only **35%** of graphs (`Δ` is *not* sign-definite) |

**By family (max `(Δ+C_hard)/C_same`):**
`dense_gnp` −0.51 · `gnp` 0.47 · `watts` 0.73 · `deg2dense` 0.94 · `degk` 0.96 ·
`chain_cliques` 0.998 · `lollipop` 1.000 · `barbell` 1.000.

Two regimes fall straight out of the split:

1. **Dense / random graphs — wide margin.** `(Δ+C_hard)/C_same` is *negative* on dense `gnp`
   (median −2.3): `Δ + C_hard < 0 < C_same`. The reservoir dwarfs the obstruction.

2. **Bottleneck families — asymptotically tight, and `C_hard = 0`.** On barbell/lollipop/glued
   cliques the sign change happens on the **bridge edge, which carries no triangles** (`t=0`), so
   **`C_hard = 0`**. The binding constraint there is purely `Δ ≤ C_same`, and it is asymptotically
   tight: stress-testing barbell up to `m=150`, `(Δ)/C_same → 0.999997` with `Q = −0.06` (still
   negative). The margin → 0⁺ as the cliques grow.

**Headline.** The hard cross-mass `C_hard` is *not* the binding obstruction — on the only graphs
where the inequality is nearly tight, `C_hard = 0`. The real fight is the **diagonal vs. the
same-sign reservoir**, `Δ ≤ C_same`, in the bottleneck regime. This relocates the difficulty:
the previous notes hunted the hard sign-crossing edges `H`; the exact decomposition shows those
edges are slack where it matters and the binding term is the triangle-rich *interior* of each
nodal domain (clique), captured globally by `Δ` and `C_same`.

## Supporting exact identities (all verified to machine zero)

These are the classical Fiedler nodal balances, confirmed exact and available as scaffolding:

- **Dirichlet split** `D₊₊ + D₋₋ + D_cross = λ₂` (unit norm), max residual `4·10⁻¹⁴`.
- **Per-domain eigen-balance** `D₊₊ + Bd₊ = λ₂·M₊` and `D₋₋ + Bd₋ = λ₂·M₋`, where
  `Bd₊ = Σ_{cross, v∈V+} f_v(f_v−f_u) ≥ 0`, `M₊ = Σ_{V+} f_v²`. Max residual `3·10⁻¹⁴`.
  (The boundary terms `Bd±` are individually `≥0` — the eigen-equation forces each domain's
  interior Dirichlet energy to be balanced by an outflow across the nodal boundary.)
- **Second moment** `fᵀL²f = λ₂²`, max residual `9·10⁻¹³`.
- **Triangle-boundary balance** `T_cross = Tbd₊ + Tbd₋`, max residual `1·10⁻¹²`.

## Status and next lever

The decomposition is **exact and useful**: it is the cleanest reduction yet, with the reservoir
global. But it does **not** close the proof — the bottleneck regime makes `Δ ≤ C_same`
asymptotically tight (ratio → 1⁻), so any sufficient bound must be tight enough to survive the
glued-clique limit. The honest next step is to prove `Δ ≤ C_same` in the bottleneck regime
(`C_hard = 0`), i.e. on graphs whose nodal domains are near-cliques; there the per-clique
structure (`τ_v ≈ d_v(d_v−1)`, `f` nearly flat) should make `Δ` and `C_same` directly comparable.

**Formalised:** the purely-algebraic master identity
`triEnergy = 2·Σ_v τ_v f_v² − 2·Σ_{i,j}[i~j] t_ij f_i f_j` (and its `−2λ·degQuad` surplus
corollary) are formalised in `Topostability/ConjectureB.lean` as `triEnergy_diag_corr` /
`triEnergy_sub_two_lam_degQuad` (no `sorry`, no spectral hypothesis; `lake env lean` clean on
Modal). `aggregate_triangle_poincare` remains open.
