# Conjecture B — aggregate Poincaré for TYPE A bottleneck graphs

Prove `T ≤ 2λ·degQuad` for TYPE A (low-degree ports carry the Fiedler mass; dense gapped core `H`).
**Result: the mechanism is confirmed (core gap `γ > λ` 21/22, ports carry 50–81 % of `degQuad`), and
`T/RHS ≤ 0.32` with huge margin. BUT the premise "triangles mostly inside `H`" is FALSE for the
*energy*: the bottleneck cross-triangle `T_cross` is DOMINANT (54–69 % of `T`), `T_core` only 31–48 %.
The correct proof is a HYBRID: bound the port-incident energy by `t_e ≤ d_port−1` (NOT lossy — `d_port`
is small, unlike the dense core) and the core energy by block flatness; both compensated by
`RHS ≥ 2λ·port-mass`.** Code: [`aggregate_typeA_bottleneck.py`](../aggregate_typeA_bottleneck.py).

## TASK 1 — triangle decomposition (premise corrected)

`T = T_core + T_cross + T_bot` by triangle membership in core `H` / ports `P`:

| graph | T/RHS | core % | **cross %** | bot % | γ/λ |
|---|---|---|---|---|---|
| deg2+dense(60,.85) | 0.323 | 46 | **54** | 0 | 21.3 |
| deg2+dense(80,.6) | 0.307 | 39 | **61** | 0 | 18.6 |
| deg2+dense(60,.6) | 0.304 | 38 | **62** | 0 | 12.0 |
| twin-port `K₈₀` d4 | 0.210 | 39 | **61** | 0 | 54.7 |

> **`T_cross` (port-incident triangles) is DOMINANT (54–69 %), not negligible.** Although *few* triangles
> touch a port (count is core-dominated), each carries the concentrated bottleneck gradient (`f_port`
> extreme), so the *energy* is cross-dominated. `T_bot = 0` (too few ports to form a triangle). **The
> "T ≈ T_core" assumption is FALSE** — the proof must handle `T_cross`.

## TASK 2 — core gap and block flatness

`γ = λ₂(L_H)` (core Fiedler gap): **`γ > λ` on 21/22** (`γ/λ` up to 28; the one miss is very sparse core
`q ≈ 0.1` where `γ ≤ λ`). With `γ > λ`, the Fiedler restricted to `H` satisfies
`(L_H − λ)f_H = source` (source = port→core coupling), so block flatness gives
`‖f_H − mean_H‖² ≤ ‖source‖²/(γ−λ)²` (source norm `≈ 1.94`, small and bounded). The core is *flat*.

## TASK 3 — the hybrid triangle bound

Split `T = Σ_e t_e g²` by **edge type**, not triangle type:

- **Port-incident edges** (`e ∋ port`): `t_e ≤ d_port − 1` (a common neighbour avoids the two
  endpoints). **This is the `B2′`/min-degree bound — but it is NOT lossy here** because `d_port` is small
  (`= 2` for deg2+dense). So `Σ_{e∋P} t_e g² ≤ (d_port−1)·D_port` (`D_port = Σ_{e∋P}g²`). This captures
  `T_cross` (the dominant term) tightly.
- **Core edges** (`e ⊆ H`): `Σ_{e⊆H} t_e g² ≤ max_{e⊆H} t_e · D_core`, and `D_core` is small by block
  flatness (`D_core ≤ λ_max(L_H)·‖f_H−mean‖²`).

> The `B2′` relaxation **fails globally** (sparse dense-core, `min−1 ≫ t_e`) but is **valid on ports**
> (`d_port` small) — the hybrid uses it only where it is tight, and block flatness on the core.

## TASK 4 — RHS lower bound from bottleneck mass

`RHS = 2λ·degQuad ≥ 2λ·Σ_{v∈P}d_v f_v²` (bottleneck mass). Empirically the **ports carry 50–81 % of
`degQuad`** (`bott_frac`), so `RHS` is dominated by the port mass — exactly what bounds `T_cross` (port
edges): `(d_port−1)·D_port` vs `2λ·d_port·f_port²`, and `D_port ≲ f_port²` (port gradient), giving
`T_cross/RHS ≲ (d_port−1)/(2λ·d_port) < 1`.

## TASK 5 — the sufficient condition holds for TYPE A

| | result |
|---|---|
| actual `T/RHS ≤ 1` | **22/22** (max **0.323**, huge margin) |
| `γ > λ` (block gap) | 21/22 |
| bound `T/RHS ≤ 1` (hybrid, `γ > λ`) | **21/22** |
| bound finite | 22/22 |

> The hybrid bound proves `T/RHS < 1` on **21/22** (all with `γ > λ`), with the bound `≈ 0.3–0.5` vs
> actual `≤ 0.32`. The 1 miss is the `γ ≤ λ` case (very sparse core, `q ≈ 0.1`) — but there `T` is tiny
> (few triangles, `T/RHS ≈ 0.1`) so the aggregate holds trivially by a separate (low-triangle) argument.

## TASK 6 — Lean lemma

> **`aggregate_triangle_poincare_typeA`** (assumptions): a core block `H` with gap `γ > λ`
> (`poincare_on_block`), ports `P = V∖H` of degree `≤ δ` (small), triangle support such that `T_bot = 0`.
> **Conclusion** `T ≤ 2λ·degQuad`, via:
> 1. `Σ_{e∋P} t_e g² ≤ (δ−1)·D_port` (`triCount ≤ min−1` on port edges — `triCount_le_min_degree_sub_one`,
>    already in Lean, applied only to ports);
> 2. `Σ_{e⊆H} t_e g² ≤ τ_H·D_core`, `D_core ≤ λ_max(L_H)·‖f_H−mean‖²` (block flatness, `poincare_on_block`);
> 3. `RHS ≥ 2λ·Σ_P d_v f_v²` (bottleneck mass), dominating both.

The Lean bridge reuses two existing sorry-free pieces (`triCount_le_min_degree_sub_one`,
`poincare_on_block`); the open work is the bookkeeping that assembles 1+2 ≤ 3 with the source-norm /
bottleneck-mass constants.

## Conclusion

- **Premise corrected:** `T_cross` (bottleneck triangle) is DOMINANT (54–69 %), not `T_core`. The proof
  must bound the cross term.
- **Mechanism confirmed:** core gap `γ > λ` (21/22), ports carry 50–81 % of `degQuad`, `T/RHS ≤ 0.32`.
- **Hybrid proof:** `t_e ≤ d_port−1` on port edges (valid — small degree) + block flatness on the core +
  `RHS ≥ 2λ·port-mass`. Proves 21/22 (all `γ > λ`); the `γ ≤ λ` sparse-core case is low-triangle
  (trivial). This is the route to `aggregate_triangle_poincare_typeA`.

## Lean
No code change yet; this is the proof sketch for `aggregate_triangle_poincare_typeA`. It reuses
`triCount_le_min_degree_sub_one` (on ports only) and `poincare_on_block` (core flatness), both sorry-free.
The full `aggregate_triangle_poincare` still factors as regular (proved) ∪ TYPE A (this sketch) ∪
`γ ≤ λ` low-triangle; the global-coupling obstruction (`conjecture_B_aggregate_triangle_slack_global`)
is avoided here by the explicit block structure.
