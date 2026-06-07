# Paper 11, Conjecture 1 (`tauG ≤ λ₂`) is **FALSE** — refuted 2026-06-07

**Statement (refuted).** For every connected graph `G` on ≥ 2 vertices,
`tauG G ≤ algebraicConnectivity G`, where
- `tauG G` = minimum over edges `(u,v)` of `|N(u) ∩ N(v)|` (min common-neighbour /
  "triangle" count over edges), and
- `algebraicConnectivity G` = `λ₂`, the second-smallest Laplacian eigenvalue.

This was `Topostability/Paper11.lean`'s last `sorry`. It is **not provable**: the
inequality is false, and false by an *unbounded* margin.

## How it was refuted

`counterexample_search.py` (repo root): exhaustive over all connected graphs up to
isomorphism for `n = 4..7` (networkx graph atlas), plus ~184k random + ~95k
structured graphs on `n = 8`.

- `n = 4, 5`: **no** counterexample (conjecture holds).
- `n = 6`: **exactly one** counterexample (up to iso): `tauG = 1`, `λ₂ ≈ 0.7639`.
- `n ≥ 6`: many, with arbitrarily large gap (see family below).

## The clean infinite family: glued cliques

Take two copies of `K_m` and identify a shared clique of `s` vertices
(`0 ≤ s < m`). Call it `K_m ∪_s K_m`, on `n = 2m − s` vertices.

- **Min triangle-degree.** Every edge lies inside some `K_m`, whose other `m − 2`
  vertices are common neighbours. Edges between two non-shared vertices realise the
  minimum, so **`tauG = m − 2`**. (Shared–shared edges have *more* common
  neighbours, `2m − s − 2 ≥ m − 2`.)
- **Algebraic connectivity.** The `s` shared vertices form a vertex cut, so
  `algebraicConnectivity ≤ κ_vertex(G) = s` (Fiedler's bound `λ₂ ≤ κ_v`). Numerically
  `λ₂ = s` exactly for this family.

Hence **`tauG − λ₂ = (m − 2) − s`**, a counterexample exactly when **`m > s + 2`**.

| shared `s` | `λ₂` | first counterexample | tauG | λ₂ | n |
|---|---|---|---|---|---|
| 1 vertex | ≤ 1 | `K₄ ∪₁ K₄` | 2 | 1 | 7 |
| 2 (an edge) | ≤ 2 | `K₅ ∪₂ K₅` | 3 | 2 | 8 |
| 2 (an edge) | ≤ 2 | `K_m ∪₂ K_m`, m→∞ | m−2 | 2 | 2m−2 |

The last row shows **`tauG − λ₂ → ∞`**: the conjecture fails by an arbitrarily
large margin. Equivalently `tauG / λ₂ ≥ (m−2)/s → ∞`.

## Cleanest minimal counterexamples

- **Smallest (n = 6).** The unique `n=6` counterexample:
  edges `(0,4),(0,5),(1,2),(1,3),(1,4),(2,3),(2,4),(4,5)`; `tauG = 1`, `λ₂ ≈ 0.7639`,
  cut vertex `4`. (Ad-hoc shape; listed for completeness.)
- **Cleanest conceptual (n = 7).** Two `K₄`'s sharing a single vertex
  (`A = {0,1,2,3}`, `B = {0,4,5,6}`): every edge is in a `K₄` so `tauG = 2`, but `0`
  is a cut vertex so `λ₂ ≤ 1`; computed `λ₂ = 1`. So `2 = tauG > λ₂ = 1`.
- **Cleanest with margin (n = 8).** Two `K₅`'s sharing an edge: `tauG = 3`, `λ₂ = 2`.

## Why the conjecture is wrong (one line)

`tauG` is a **local** density measure (triangles per edge); `λ₂` is bounded by
**global** connectivity (`λ₂ ≤ κ_vertex`). Gluing dense cliques along a thin cut
drives local density above global connectivity. There is no inequality in this
direction. (The *opposite-flavoured* bound — a weak `λ₂` lower bound from `tauG` —
is what `lambda2_lower_bound` in `Tests.lean` actually gives, and it is far weaker.)

## Consequence for the Lean development

The `sorry` in `conjecture_tauG_le_algebraicConnectivity` asserts a false statement;
a `sorry` there is a soundness hazard (it would let `False` be derived if ever
`exact`-ed against a concrete counterexample). It must be removed. Proposed:

1. **Keep** the proved facts: `algebraicConnectivity_nonneg`, and the `tauG = 0`
   sub-case (true and useful — covers triangle-free graphs).
2. **Replace** the false general theorem with either
   (a) a documented `-- REFUTED` note + the `tauG = 0` lemma as the salvaged result, or
   (b) additionally **formalize the counterexample in Lean** (e.g. two `K₄` sharing
   a vertex on `Fin 7`, or `K₅ ∪₂ K₅` on `Fin 8`) as a `theorem
   not_forall_tauG_le_algebraicConnectivity`, turning the refutation into a checked
   result. This is the rigorous, publishable artifact.
