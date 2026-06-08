# Simplicial hierarchy: extending T(G) to tetrahedra — `T₃(K)`

**Definition.** For a 3-dimensional simplicial complex `K`, the *tetrahedral graph* `T₃(K)` has the **triangles (2-faces) of `K`** as vertices; two triangles are adjacent iff they **share an edge and both lie in a common tetrahedron** of `K`. This is the exact dimension-shifted analogue of the triangle graph `T(G)` (whose vertices are edges, adjacent when they share a vertex and lie in a common triangle).

**Dimensional ladder of algebraic connectivities:**

| level | graph | vertices are | adjacency via | λ₂ |
|---|---|---|---|---|
| 0→1 | `G` (1-skeleton) | vertices | edges | `λ₂(G)` |
| 1→2 | `T(G)` | edges | triangles | `λ₂(T(G))` |
| 2→3 | `T₃(K)` | triangles | tetrahedra | `λ₂(T₃(K))` |

**Conjectured simplicial hierarchy:**  `λ₂(T₃(K)) ≤ λ₂(T(G)) ≤ λ₂(G)`.

## Test complexes

- Total generated: **1038**; with all three graphs connected (eligible for the chain): **333**.
  - **K_n clique**: 4 generated, 4 fully connected.
  - **3-sphere**: 2 generated, 2 fully connected.
  - **stacked 3-sphere**: 32 generated, 32 fully connected.
  - **random 3-complex**: 1000 generated, 295 fully connected.

## Hierarchy results

- **Full chain `λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)` holds on 333/333 (100.00%).**
- **Lower link `λ₂(T₃(K)) ≤ λ₂(T(G))`** (new): ✅ 0 violations.
  - Tightest ratio λ₂(T₃)/λ₂(T(G)) = 1.0000 (`K5`, λ₂(T₃)=5.0000, λ₂(T(G))=5.0000).
- **Upper link `λ₂(T(G)) ≤ λ₂(G)`** (= Conjecture B): ✅ 0 violations.
  - Tightest ratio λ₂(T(G))/λ₂(G) = 1.0000 (`K8`, λ₂(T(G))=8.0000, λ₂(G)=8.0000).

## Correlations (Pearson) among the three λ₂

| pair | r |
|---|---|
| λ₂(G) vs λ₂(T(G)) | 0.9547 |
| λ₂(G) vs λ₂(T3(K)) | 0.7290 |
| λ₂(T(G)) vs λ₂(T3(K)) | 0.8055 |

## Worked examples

### Complete clique complexes `K_n` (T(G)=J(n,2), T₃(K)=J(n,3))

| complex | V | E | Tri | Tet | λ₂(G) | λ₂(T(G)) | λ₂(T₃(K)) | chain |
|---|---|---|---|---|---|---|---|---|
| K5 | 5 | 10 | 10 | 5 | 5.000 | 5.000 | 5.000 | ✅ |
| K6 | 6 | 15 | 20 | 15 | 6.000 | 6.000 | 6.000 | ✅ |
| K7 | 7 | 21 | 35 | 35 | 7.000 | 7.000 | 7.000 | ✅ |
| K8 | 8 | 28 | 56 | 70 | 8.000 | 8.000 | 8.000 | ✅ |

Johnson graphs satisfy `λ₂(J(n,k)) = n` for every `k`, so the clique complex of `K_n` gives **equality throughout**: `λ₂(T₃)=λ₂(T(G))=λ₂(G)=n`. The hierarchy is tight (ratio 1) on the densest complexes.

### Triangulated 3-spheres

| complex | V | E | Tri | Tet | λ₂(G) | λ₂(T(G)) | λ₂(T₃(K)) | chain |
|---|---|---|---|---|---|---|---|---|
| boundary-4simplex | 5 | 10 | 10 | 5 | 5.000 | 5.000 | 5.000 | ✅ |
| cross-polytope-16cell | 8 | 24 | 32 | 16 | 6.000 | 4.000 | 2.000 | ✅ |
| stacked-k1-0 | 6 | 14 | 16 | 8 | 4.000 | 3.000 | 2.000 | ✅ |
| stacked-k1-1 | 6 | 14 | 16 | 8 | 4.000 | 3.000 | 2.000 | ✅ |
| stacked-k1-2 | 6 | 14 | 16 | 8 | 4.000 | 3.000 | 2.000 | ✅ |
| stacked-k1-3 | 6 | 14 | 16 | 8 | 4.000 | 3.000 | 2.000 | ✅ |
| stacked-k2-0 | 7 | 18 | 22 | 11 | 3.586 | 2.327 | 1.209 | ✅ |
| stacked-k2-1 | 7 | 18 | 22 | 11 | 3.586 | 2.327 | 1.209 | ✅ |
| stacked-k2-2 | 7 | 18 | 22 | 11 | 3.586 | 2.327 | 1.209 | ✅ |
| stacked-k2-3 | 7 | 18 | 22 | 11 | 3.586 | 2.327 | 1.209 | ✅ |

## Conclusion

- **The simplicial hierarchy `λ₂(T₃(K)) ≤ λ₂(T(G)) ≤ λ₂(G)` holds on every one of the 333 fully-connected test complexes** — clique complexes, random 3-complexes, and triangulated 3-spheres alike.
- The new **lower link `λ₂(T₃(K)) ≤ λ₂(T(G))`** is the dimensional successor of Conjecture B; empirically it behaves the same way (no counterexample), suggesting a general *spectral monotonicity up the simplicial ladder*: algebraic connectivity does not increase as you pass from `k`-faces to `(k+1)`-faces via shared-facet/common-cofacet adjacency.
- Equality is attained by the densest complexes (complete clique complexes, Johnson graphs, λ₂ = n at every level).

## Caveats

- Exploration only — clique complexes (n=5..8), ~600 random 3-complexes, and a family of triangulated 3-spheres (boundary of the 4-simplex, the 16-cell, and stacked spheres). Not a census; no proofs.
- `T(G)` uses the existing graph definition (3-cliques of the 1-skeleton); `T₃(K)` uses `K`'s actual 2-faces and tetrahedra. Both coincide with the simplicial faces for clique complexes. `λ₂` numerical (`eigvalsh`), tol 1e-9.

