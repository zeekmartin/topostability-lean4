# JEPA-spectral test — simplicial hierarchy on neural-net-like graphs

**Question.** The repo's spectral simplicial hierarchy `λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)` was validated on dense random graphs, complete-clique complexes, and triangulated 3-spheres. Does it still hold on graphs shaped like the connectivity of neural-network layers (JEPA-style encoders: layered, residual/skip, attention hubs)?

**Setup.** Four families, `n ∈ [20,50]`, generated until **125 eligible** (`T(G)`-connected) graphs per family (**500 eligible / 1640 connected graphs** total). For each we build `T(G)` (triangle graph, 3-cliques of `G`) and `T₃` (tetrahedral graph of `G`'s clique complex; triangles adjacent when they share an edge and span a common 4-clique). `λ₂` is the 2nd-smallest Laplacian eigenvalue (`eigvalsh`, tol 1e-9).

| family | proxy for | generator |
|---|---|---|
| `layered` | feed-forward depth + skip/residual | dense multipartite (p≈.85) + i→i+2 skips |
| `small-world` | local windows + long-range | Watts–Strogatz (k∈{8,10,12}, low rewiring) |
| `random-regular` | unstructured baseline | random d-regular (d∈{10,12,14}) |
| `scale-free` | attention hubs | powerlaw-cluster / Holme–Kim (m∈{4,5,6}) |

## Coverage & yield

`T(G)` is connected only when essentially every edge of `G` lies in a triangle; `T₃` additionally needs 4-cliques (tetrahedra). **Yield** = fraction of connected `G` whose `T(G)` is also connected — a measure of how triangle-rich each topology is.

| family | conn. G | T(G) conn. | yield | T₃ conn. | mean transitivity |
|---|---|---|---|---|---|
| layered | 363 | 125 | 34.4% | 0 | 0.263 |
| small-world | 632 | 125 | 19.8% | 103 | 0.569 |
| random-regular | 252 | 125 | 49.6% | 17 | 0.350 |
| scale-free | 393 | 125 | 31.8% | 4 | 0.385 |

## Does the hierarchy still hold?

- **Upper link `λ₂(T(G)) ≤ λ₂(G)` (Conjecture B): ✅ 0 violations out of 500 graphs with `T(G)` connected.**
- **Full chain `λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)`: holds on 53/53 graphs where `T₃` is connected** (lower-link `λ₂(T₃) ≤ λ₂(T(G))` violations: 0 ✅).

## Coherence ratio  ρ = λ₂(T(G)) / λ₂(G)  per family

ρ ≤ 1 always (that *is* the upper link). The **smaller** ρ, the **steeper the coherence drop** when lifting from vertices to edges.

| family | n | mean ρ | median ρ | min ρ | max ρ | std |
|---|---|---|---|---|---|---|
| layered | 125 | 0.2309 | 0.2172 | 0.0806 | 0.3906 | 0.0714 |
| small-world | 125 | 0.2384 | 0.2407 | 0.1210 | 0.3389 | 0.0407 |
| random-regular | 125 | 0.2302 | 0.2033 | 0.0821 | 0.5117 | 0.1099 |
| scale-free | 125 | 0.2585 | 0.2469 | 0.1039 | 0.5790 | 0.0838 |

## Which family has the steepest coherence drop?

Ranked by mean ρ (steepest first; ± = standard error of the mean):

1. **random-regular** — mean ρ = 0.2302 ± 0.0098
2. **layered** — mean ρ = 0.2309 ± 0.0064
3. **small-world** — mean ρ = 0.2384 ± 0.0036
4. **scale-free** — mean ρ = 0.2585 ± 0.0075

- **The three lowest families are a statistical tie** (`random-regular`, `layered`, `small-world`): their mean ρ differ by less than the standard error, so no single one is meaningfully the *steepest*. The drop from vertices to edge-interactions is large (~75–77%) and roughly **structure-independent** in this regime.
- **Flattest (clearly separated): `scale-free`** — `T(G)` tracks `G` most closely; hub structure best preserves algebraic connectivity under the lift to the interaction graph.

## Takeaways

- **The hierarchy survives JEPA-like topology.** No violation of the upper link in any family; the full chain holds wherever `T₃` exists. Spectral monotonicity up the simplicial ladder is not an artifact of dense/random graphs — it persists on sparse, layered, hub-heavy wiring.
- `T₃` is mostly **absent on feed-forward/regular wiring** (too few 4-cliques); it appears chiefly in high-clustering small-world graphs. So the 2→3 rung of the ladder is only testable where the topology is locally dense — exactly the clustered regime.
- The coherence ratio ρ gives a one-number summary of how much algebraic connectivity is *lost* moving from nodes to edge-interactions; it discriminates the families even though the inequality itself never breaks.

## Caveats

- Exploration only, no proofs. ~500 graphs, single seed (20260609), `n ∈ [20,50]`. `T(G)`/`T₃` use the existing repo definitions (cliques of `G`). Ratios computed only over graphs where the relevant graph is connected; families differ in how often that holds (see Coverage).
- 'JEPA-like' is a structural analogy (layered + skip + hubs), not a real trained-network connectivity graph.

