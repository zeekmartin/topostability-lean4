# Conjecture B — direct proof of `aggregate_triangle_poincare` (`T ≤ 2λ·degQuad`)

Attack `T = Σ_e t_e g² ≤ 2λ·degQuad` directly (no `B2′`, no `t_e ≤ min−1`). **Result: the aggregate
holds robustly (41/41), the extremal family is `K_n`/dense-regular (T/RHS → 1, the PROVEN case), and all
irregular graphs are strictly below (≤ 0.69). But every elementary direct route FAILS: the
subgraph≤complete (`K_{N(c)}`) bound needs `A ≥ λ(d_eff−λ)` which fails 8/41 (bound overshoots ×26 on
sparse cores); the `λ_max` local bound is too lossy (13/41); and the per-apex local Poincaré
`E_{N(c)} ≤ 2λ·P_c` fails 0.9%. The aggregate genuinely needs the global apex coupling.** Code:
[`aggregate_triangle_poincare_direct.py`](../aggregate_triangle_poincare_direct.py).

## TASK 1 — triangle / apex expansion (exact)

`t_e = #triangles on e`, so `T = Σ_e t_e g² = Σ_{triangles abc}(g_{ab}²+g_{bc}²+g_{ca}²)`. Regrouping by
apex (the third vertex):

> **`T = Σ_c E_{G[N(c)]}(f)`** where `E_{G[N(c)]} = Σ_{a,b∈N(c), a∼b}(f_a−f_b)²` is the Dirichlet
> energy of `f` on the induced neighbourhood subgraph.

Since `Σ_c P_c = degQuad` (`P_c = Σ_{v∈N(c)}f_v²`, each `v` counted `d_v` times), the target is the
**aggregate local Poincaré** `Σ_c E_{G[N(c)]} ≤ 2λ·Σ_c P_c`.

## TASK 5 — extremal family (the true one, for `T` not `B2′`)

`T ≤ 2λ·degQuad` holds **41/41**. Tightest:

| graph | class | `T/(2λ·degQuad)` |
|---|---|---|
| `K₅₀` | REGULAR | **0.980** |
| `K₃₀` | REGULAR | 0.966 |
| cocktail₆ | multipartite | 0.800 |
| gnp(40,.7) | RANDOM | 0.693 |
| deg2+dense(60,.9) | TYPE A | 0.652 |

> **Extremal = `K_n`/dense-regular, `T/RHS = (n−2)/(n−1) → 1`** — exactly where the regular case is
> PROVEN (`aggregate_triangle_poincare_regular`). All *irregular* graphs are `≤ 0.69` (well below). So
> the open content sits strictly inside the regular extremizer — unlike `B2′` (which blew past 1 on
> sparse cores), `T` itself never overshoots.

## TASK 3 — local/per-triangle bounds all FAIL

**(K) subgraph ≤ complete.** `E_{G[N(c)]} ≤ E_{K_{N(c)}} = d_c·P_c − (Σ_{N(c)}f)²`, and the Fiedler
row-sum `Σ_{N(c)}f = (d_c−λ)f_c` gives `T ≤ Σ_v s_v f_v² − Σ_c(d_c−λ)²f_c²` (`s_v = Σ_{u∼v}d_u`). This
implies the aggregate **iff `A ≥ λ(d_eff−λ)`** (`A = Σ_v(d_v²−s_v)f_v²`, signed assortativity):

| condition | holds |
|---|---|
| `A ≥ λ(d_eff−λ)` (K-route valid) | **8/41** |
| K-bound `≤ RHS` | 8/41 (K-bound/RHS up to **26**) |

> The `K_{N(c)}` bound is **tight at `K_n`** (where `G[N(c)]` is complete) but **wildly lossy when
> `G[N(c)]` is sparse** (deg2+dense: ×26 overshoot, `cond_K = −145`). Dead — same failure mode as `B2′`.

**(λ_max) local Poincaré.** `E_{N(c)} ≤ λ_max(L_{G[N(c)]})·Var_{N(c)}(f)`: aggregate `≤ RHS` only
**13/41** (max ×25). The induced-subgraph `λ_max` is not controlled by the global `λ`.

**Per-triangle charging to degrees** gives `Σ_v d_v f_v²·(#triangles through v)`, not `2λ·degQuad` (the
`λ` is the global Dirichlet, not a triangle count) — no clean per-triangle route.

## TASK 2 — per-apex local Poincaré

`E_{G[N(c)]} ≤ 2λ·P_c` per apex: **fails 15/1728 (0.9%)** of apices (corpus-dependent; lower than the
`~6%` quoted in the old docstring). The aggregate `Σ_c E_{N(c)} ≤ 2λ·Σ_c P_c` holds because the few
over-apices are compensated by apices with `E_{N(c)} ≪ 2λ·P_c`.

> **The compensation is the irreducible global coupling**: no per-apex (or per-triangle, or subgraph)
> bound suffices — the proof must aggregate over apices using the *global* eigenvector relation.

## Conclusion

- **`T = Σ_c E_{G[N(c)]}` (apex expansion, exact);** target = aggregate local Poincaré
  `Σ_c E_{N(c)} ≤ 2λ·Σ_c P_c`.
- **Extremal = `K_n`/dense-regular** (`T/RHS → 1`, PROVEN); all irregular `≤ 0.69`. `T` never overshoots
  (unlike `B2′`).
- **All elementary direct routes FAIL:** `K_{N(c)}` subgraph bound (×26 lossy, `A ≥ λ(d_eff−λ)` fails
  8/41), `λ_max` local (×25), per-apex local Poincaré (0.9% violations). The aggregate needs the
  **global apex coupling** (compensation across apices via the eigenvector).
- This is the irreducible open core; the regular extremizer is proved, and the direct proof requires a
  genuinely aggregate (not local) Poincaré argument.

## Lean
No change: `aggregate_triangle_poincare` stays the direct sorry on the TRUE `T ≤ 2λ·degQuad` (correct
after the `B2′` revert). The apex expansion `T = Σ_c E_{G[N(c)]}` (`apex_triangle_energy_identity`,
`Paper15`) is the entry point; the open step is the aggregate local Poincaré, which resists all per-apex
/ per-triangle / subgraph relaxations and needs the global eigenvector coupling. Regular case proved
(`aggregate_triangle_poincare_regular`).
