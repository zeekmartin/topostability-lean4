# Conjecture B exploration — `λ₂(T(G)) ≤ λ₂(G)`

Computational study of **Conjecture B** (Paper 14, the triangle-graph spectral gap inequality): for `G` with `T(G)` connected, the algebraic connectivity of the triangle graph never exceeds that of `G`. `T(G)` has the edges of `G` as vertices, two adjacent iff they are two sides of a common triangle (`counterexample_search.triangle_graph`, `Topostability.triangleGraph`).

Define the **gap ratio** `Q(G) = λ₂(G) / λ₂(T(G))`. Conjecture B says `Q(G) ≥ 1`; `Q = 1` is equality (tightest), `Q < 1` would be a counterexample. *Near-violations* are graphs with `Q` closest to `1`.

## Sample

Graphs from the hierarchy search (`counterexample_search._gen_graphs_hier`, n≤7 exhaustive up to iso, n=8,9 structured + random):

- n=4 (exhaustive): 6 connected graphs
- n=5 (exhaustive): 21 connected graphs
- n=6 (exhaustive): 112 connected graphs
- n=7 (exhaustive): 853 connected graphs
- n=8 (sampled): 42838 connected graphs
- n=9 (sampled): 29123 connected graphs

- **45196 have `T(G)` connected with `λ₂(T(G)) > 0`** (eligible for `Q`).
- Of these, **1525 are regular**, 43671 irregular.
- **Violations of B (`Q < 1`): 0.**  Graphs with exact equality `Q = 1`: 1491 (all regular).

## 1. Twenty tightest graphs overall (Q closest to 1)

| # | tag | n | m | Q | λ₂(T) | λ₂(G) | Δ | δ | regular? | degree sequence |
|---|-----|---|---|---|-------|-------|---|---|----------|-----------------|
| 1 | `circ8-(1, 2, 3, 4)` | 8 | 28 | 1.000000 | 8.0000 | 8.0000 | 7 | 7 | **reg** | 7,7,7,7,7,7,7,7 |
| 2 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 3 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 4 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 5 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 6 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 7 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 8 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 9 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 10 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 11 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 12 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 13 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 14 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 15 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 16 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 17 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 18 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 19 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |
| 20 | `rand9` | 9 | 36 | 1.000000 | 9.0000 | 9.0000 | 8 | 8 | **reg** | 8,8,8,8,8,8,8,8,8 |

Edges of the single tightest graph (`circ8-(1, 2, 3, 4)`): `[(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]`.

## 1b. Twenty tightest *irregular* graphs (the interesting regime)

Equality `Q = 1` is reached only by (some) regular graphs, so the tightest-overall table is dominated by `Q = 1` regulars. The genuinely informative near-violations are the tightest **irregular** graphs:

| # | tag | n | m | Q | λ₂(T) | λ₂(G) | Δ | δ | Δ−δ | degree sequence |
|---|-----|---|---|---|-------|-------|---|---|-----|-----------------|
| 1 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 2 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 3 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 4 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 5 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 6 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 7 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 8 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 9 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 10 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 11 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 12 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 13 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 14 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 15 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 16 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 17 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 18 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 19 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |
| 20 | `rand9` | 9 | 35 | 1.166667 | 6.0000 | 7.0000 | 8 | 7 | 1 | 8,8,8,8,8,8,8,7,7 |

## 2. Characterisation of near-violations

- Among the **100 tightest** graphs (smallest `Q`): **100 regular**, 0 almost-regular (Δ−δ ≤ 1, not regular), 0 more irregular.
- The minimum `Q` over irregular graphs is **1.166667** (`rand9`), strictly above 1 — irregular graphs keep a real spectral gap `λ₂(G) − λ₂(T) = 1.0000 > 0`.
- Mean `Q`: regular **1.0421**, irregular **2.2712**. Equality clusters on regular graphs; irregularity pushes `Q` up (`λ₂(T)` drops below `λ₂(G)`).
- **Regularity is necessary but not sufficient for equality.** Every one of the 1491 exact-equality (`Q = 1`) graphs is regular, but the converse fails: many *regular* graphs have `Q > 1` (e.g. the octahedron `K_{2,2,2}` = `circ6[1,2]`, 4-regular, has `Q = 2.0`; see §4). Equality is attained by the **complete graphs `K_n`** (`λ₂ = n` at every level of the ladder — the Johnson-graph fact `λ₂(J(n,k)) = n`), which is what the equality cases in the random sample collapse onto (repeated `K_8`, `K_9`).
- **Structural reading.** Conjecture B is already *proved for regular `G`* (the inequality, not equality): for `d`-regular `G` the unsigned incidence lift `h(e) = φ(u)+φ(v)` of the Fiedler vector `φ` satisfies `Σ_e h(e) = d·Σ_v φ(v) = 0`, so `h ∈ 1^⟂` of `T(G)` and its `T(G)`-Rayleigh quotient upper-bounds `λ₂(T) ≤ λ₂(G)`. Irregularity breaks that orthogonality (`Σ_v deg(v)φ(v) ≠ 0`), which is exactly why the irregular case is open — yet empirically `λ₂(T)` still stays below `λ₂(G)` with a clear margin (min irregular `Q = 1.167`).

## 3. Rayleigh route (plan Route R / Prop 6.3-style PSD test)

For connected `G`, let `B` be the **signed vertex–edge incidence matrix** (`|V|×|E|`); its columns index the vertices of `T(G)`, and `range(B) = 1^⟂`. Form

```
  M(G) = Bᵀ L_G B  −  λ₂(T(G)) · Bᵀ B          (|E|×|E|, symmetric)
```

For any edge-vector `h`, `hᵀ M h = (Bh)ᵀ L_G (Bh) − λ₂(T)|Bh|² ≥ (λ₂(G) − λ₂(T))|Bh|²`, since `Bh ∈ 1^⟂` forces `(Bh)ᵀL_G(Bh) ≥ λ₂(G)|Bh|²`. Hence **`M ⪰ 0` iff Conjecture B holds**; `M` has a forced kernel of dimension `m−n+1` (the cycle space `ker B`), and the nonzero generalised eigenvalues of `(BᵀL_G B, BᵀB)` are exactly the nonzero Laplacian eigenvalues of `G` (smallest = `λ₂(G)`).

PSD test on the 20 tightest graphs overall (mostly `Q = 1` regulars):

| tag | n | m | Q | λ₂(T) | min eig M | PSD? | #zero eig | cycle rank m−n+1 | min pos eig |
|-----|---|---|---|-------|-----------|------|-----------|------------------|-------------|
| `circ8-(1, 2, 3, 4)` | 8 | 28 | 1.0000 | 8.0000 | -5.00e-30 | ✅ | 28 | 21 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |
| `rand9` | 9 | 36 | 1.0000 | 9.0000 | -3.08e-29 | ✅ | 36 | 28 | — |

PSD test on the 20 tightest *irregular* graphs (all `Q > 1` strict):

| tag | n | m | Q | λ₂(T) | min eig M | PSD? | #zero eig | cycle rank m−n+1 | min pos eig |
|-----|---|---|---|-------|-----------|------|-----------|------------------|-------------|
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |
| `rand9` | 9 | 35 | 1.1667 | 6.0000 | -9.71e-15 | ✅ | 27 | 27 | 7.0000 |

- **`M(G) ⪰ 0` on all 40 tested tight graphs** (no PSD failures). The smallest eigenvalue is numerically `0`, confirming PSD.
- **Strict graphs (`Q > 1`, the irregular table):** `#zero eig = m−n+1` exactly (holds on every strict row), i.e. `ker M = ker B` is precisely the cycle space — the lift is faithful on `1^⟂`, and the **smallest positive eigenvalue** is the binding margin, bounded away from 0.
- **Equality graphs (`Q = 1`, the overall table):** `M ≈ 0` collapses entirely — every eigenvalue is `0`, so `#zero eig = m` exceeds the cycle rank and there is no positive eigenvalue (`—`). This is the degenerate boundary where `λ₂(T) = λ₂(G)`: the Fiedler-lift modes join the kernel.
- **Caveat on the route.** With the signed incidence `B`, `M ⪰ 0` is *equivalent* to B, so this PSD test is a re-encoding, not an independent proof — but it isolates the analytic core: a proof needs `(Bh)ᵀL_G(Bh) ≥ λ₂(T)|Bh|²` for all `h`, i.e. that `λ₂(T)` never exceeds the Rayleigh quotient of `L_G` on the incidence image. The unsigned lift (`B[u,e]=B[v,e]=1`) is the one that *proves* the regular case but leaves `1^⟂` only when `G` is regular — which is exactly why the irregular case is open.

## 4. Vertex-transitive graphs, n = 6..12

All circulant graphs `C_n(S)` (every circulant is vertex-transitive; deduped by Weisfeiler–Lehman hash) plus named vertex-transitive graphs (Petersen, 3-cube, octahedron, Johnson `J(5,2)`, complete multipartite with equal parts). **40 distinct graphs**, 27 with `T(G)` connected.

- **Violations of B among vertex-transitive graphs: 0.** Every vertex-transitive graph tested satisfies `Q ≥ 1`.
- **7 of 27 reach equality `Q = 1` — and every one of them is a complete graph `K_n`** (the `Q = 1` rows below are exactly `circ_n[1..⌊n/2⌋] = K_n`). Vertex-transitivity alone does *not* force equality: the octahedron `circ6[1,2]` (`K_{2,2,2}`, 4-regular, vertex-transitive) has `Q = 2.0`, and many other vertex-transitive circulants sit well above 1. Equality is the **complete-graph** phenomenon (`λ₂ = n` throughout), not a general symmetry effect.

Tightest 20 (smallest Q) vertex-transitive graphs:

| name | n | m | deg | Q | λ₂(T) | λ₂(G) |
|------|---|---|-----|---|-------|-------|
| `circ8[1, 2, 3, 4]` | 8 | 28 | 7 | 1.000000 | 8.0000 | 8.0000 |
| `circ11[1, 2, 3, 4, 5]` | 11 | 55 | 10 | 1.000000 | 11.0000 | 11.0000 |
| `circ6[1, 2, 3]` | 6 | 15 | 5 | 1.000000 | 6.0000 | 6.0000 |
| `circ12[1, 2, 3, 4, 5, 6]` | 12 | 66 | 11 | 1.000000 | 12.0000 | 12.0000 |
| `circ7[1, 2, 3]` | 7 | 21 | 6 | 1.000000 | 7.0000 | 7.0000 |
| `circ9[1, 2, 3, 4]` | 9 | 36 | 8 | 1.000000 | 9.0000 | 9.0000 |
| `circ10[1, 2, 3, 4, 5]` | 10 | 45 | 9 | 1.000000 | 10.0000 | 10.0000 |
| `circ12[1, 2, 3, 4, 5]` | 12 | 60 | 10 | 1.250000 | 8.0000 | 10.0000 |
| `circ10[1, 2, 3, 4]` | 10 | 40 | 8 | 1.333333 | 6.0000 | 8.0000 |
| `circ8[1, 2, 3]` | 8 | 24 | 6 | 1.500000 | 4.0000 | 6.0000 |
| `circ12[1, 2, 3, 4, 6]` | 12 | 54 | 9 | 1.699056 | 4.7085 | 8.0000 |
| `circ11[1, 2, 3, 4]` | 11 | 44 | 8 | 1.818039 | 3.8949 | 7.0810 |
| `circ10[1, 2, 3, 5]` | 10 | 35 | 7 | 1.877640 | 3.3989 | 6.3820 |
| `circ6[1, 2]` | 6 | 12 | 4 | 2.000000 | 2.0000 | 4.0000 |
| `circ9[1, 2, 3]` | 9 | 27 | 6 | 2.393670 | 2.1392 | 5.1206 |
| `circ12[1, 2, 3, 4]` | 12 | 48 | 8 | 2.594467 | 2.4159 | 6.2679 |
| `circ12[1, 2, 3, 6]` | 12 | 42 | 7 | 3.071391 | 1.7152 | 5.2679 |
| `circ8[1, 2, 4]` | 8 | 20 | 5 | 3.414214 | 1.1716 | 4.0000 |
| `circ10[1, 2, 3]` | 10 | 30 | 6 | 4.299583 | 1.0192 | 4.3820 |
| `circ11[1, 2, 3]` | 11 | 33 | 6 | 4.402292 | 0.8567 | 3.7713 |

- 20 vertex-transitive graphs have `Q > 1` strictly (triangle graph spectrally strictly below `G`). These are the vertex-transitive graphs whose Fiedler eigenspace is **not** preserved by the incidence lift (e.g. bipartite circulants with few triangles, where `T(G)` is sparse or disconnected-leaning).

## Conclusion

- **Conjecture B survives every test here:** `Q(G) ≥ 1` on all 45196 hierarchy-search graphs with `T(G)` connected and on all 27 vertex-transitive graphs (n=6..12). **Zero violations.**
- **Equality `Q = 1` is the complete-graph phenomenon.** All 1491 exact-equality graphs are regular (regularity is *necessary*), but regularity is *not sufficient* — the 4-regular octahedron has `Q = 2`. Equality is realised by `K_n` (`λ₂ = n` at every ladder level). Off the complete graphs the gap opens up: the tightest *irregular* graph has `Q = 1.1667`, and the proved-regular / open-irregular split of Conjecture B concerns the *inequality*, which holds throughout.
- **The Rayleigh PSD reformulation holds exactly:** `Bᵀ L_G B − λ₂(T)·BᵀB ⪰ 0` (signed incidence `B`) on every tight graph, with kernel = cycle space. This pins the open irregular case to a single analytic statement — the incidence lift of any test vector keeps a Rayleigh quotient on `L_G` at least `λ₂(T(G))`.

## Caveats

- Sample is the hierarchy search (n≤7 exhaustive up to iso; n=8,9 sampled, not exhaustive) + circulant/named vertex-transitive graphs n=6..12. Not a census of vertex-transitive graphs (which is itself hard); circulants + named families only.
- `λ₂` and eigenvalues numerical (`numpy.linalg.eigvalsh`), tol 1e-9 (1e-6 for the PSD min-eigenvalue check). Empirical observations, not proofs.

