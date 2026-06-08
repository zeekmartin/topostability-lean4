# Simplicial tower to `T₄` — does spectral monotonicity persist?

Extends [`simplicial_hierarchy_T3.md`](simplicial_hierarchy_T3.md) one rung higher. `T₄(K)` has the **tetrahedra of `K`** as vertices; two tetrahedra are adjacent iff they **share a triangle and lie in a common 4-simplex (pentatope)** of `K` — the dimension-4 analogue of the same shared-facet / common-cofacet rule.

| level | graph | vertices are | adjacency via | λ₂ |
|---|---|---|---|---|
| 0→1 | `G` | vertices | edges | `λ₂(G)` |
| 1→2 | `T(G)` | edges | triangles | `λ₂(T(G))` |
| 2→3 | `T₃(K)` | triangles | tetrahedra | `λ₂(T₃(K))` |
| 3→4 | `T₄(K)` | tetrahedra | 4-simplices | `λ₂(T₄(K))` |

## TEST 3 — complete clique complexes `K_n` (Johnson anchor)

For the clique complex of `K_n`, every level is a Johnson graph `T=J(n,2)`, `T₃=J(n,3)`, `T₄=J(n,4)`, and `λ₂(J(n,k)) = n` for all `k`. So **λ₂ should equal `n` at all four levels.**

| complex | n | λ₂(G) | λ₂(T(G)) | λ₂(T₃) | λ₂(T₄) | all = n? |
|---|---|---|---|---|---|---|
| K5 | 5 | 5.000 | 5.000 | 5.000 | 5.000 | ✅ |
| K6 | 6 | 6.000 | 6.000 | 6.000 | 6.000 | ✅ |
| K7 | 7 | 7.000 | 7.000 | 7.000 | 7.000 | ✅ |
| K8 | 8 | 8.000 | 8.000 | 8.000 | 8.000 | ✅ |
| K9 | 9 | 9.000 | 9.000 | 9.000 | 9.000 | ✅ |

➡️ **Confirmed:** λ₂ = n at all four levels for every K_n (n=5..9). The Johnson-graph property is the exact theoretical anchor, and the numerics reproduce it.

## TEST 1 — the `T₄` tower  λ₂(T₄) ≤ λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)

Over **198** complexes with all four graphs connected (clique complexes `K_{5..9}` + random 4-complexes):

- **Full 4-level tower holds on 198/198 (100.00%).**
- New top link `λ₂(T₄) ≤ λ₂(T₃)`: ✅ 0 violations.
- `λ₂(T₃) ≤ λ₂(T(G))`: ✅ 0 violations.
- `λ₂(T(G)) ≤ λ₂(G)`: ✅ 0 violations.

Example values (clique complexes, all four levels):

| complex | V | Tet | Penta | λ₂(G) | λ₂(T) | λ₂(T₃) | λ₂(T₄) |
|---|---|---|---|---|---|---|---|
| K5 | 5 | 5 | 1 | 5.000 | 5.000 | 5.000 | 5.000 |
| K6 | 6 | 15 | 6 | 6.000 | 6.000 | 6.000 | 6.000 |
| K7 | 7 | 35 | 21 | 7.000 | 7.000 | 7.000 | 7.000 |
| K8 | 8 | 70 | 56 | 8.000 | 8.000 | 8.000 | 8.000 |
| K9 | 9 | 126 | 126 | 9.000 | 9.000 | 9.000 | 9.000 |
| rand4-n9-p0.95-q0.70 | 9 | 105 | 65 | 7.000 | 6.000 | 5.000 | 2.229 |
| rand4-n6-p0.97-q0.85 | 6 | 15 | 5 | 6.000 | 6.000 | 6.000 | 3.209 |
| rand4-n6-p0.87-q0.90 | 6 | 9 | 2 | 4.000 | 3.000 | 2.000 | 1.000 |
| rand4-n8-p0.93-q0.72 | 8 | 23 | 8 | 3.697 | 2.486 | 1.488 | 0.663 |
| rand4-n7-p0.84-q0.87 | 7 | 25 | 9 | 5.000 | 4.000 | 3.000 | 1.334 |

## TEST 2 — decay ratios up the tower

`r₁ = λ₂(T(G))/λ₂(G)`, `r₂ = λ₂(T₃)/λ₂(T(G))`, `r₃ = λ₂(T₄)/λ₂(T₃)`. By the hierarchy each is `≤ 1`; the question is whether they have a non-trivial lower bound and whether they are constant for symmetric objects.

| ratio | n | min | median | mean | max |
|---|---|---|---|---|---|
| r₁ = λ₂(T)/λ₂(G) | 1234 | 0.0663 | 0.6215 | 0.6288 | 1.0000 |
| r₂ = λ₂(T₃)/λ₂(T) | 848 | 0.2070 | 0.6058 | 0.6103 | 1.0000 |
| r₃ = λ₂(T₄)/λ₂(T₃) | 198 | 0.2075 | 0.5000 | 0.5653 | 1.0000 |

**Constant for symmetric objects?**
- **Complete clique complexes** (the most symmetric — full simplex skeleta): `λ₂ = n` at every level, so **`r₁ = r₂ = r₃ = 1` exactly**. The ratio is constant (= 1) for these.
- **Cross-polytope (16-cell)**: λ₂(G)=6.000, λ₂(T)=4.000, λ₂(T₃)=2.000 → r₁=0.667, r₂=0.500 — clean rationals (2/3, 1/2), but **not** constant across levels.
- **Universal bound:** every observed ratio lies in (0, 1]; the smallest seen are r₁≈0.066, r₂≈0.207, r₃≈0.208. No ratio ever exceeded 1 (the monotonicity), but there is **no constant decay factor** in general — the drop depends on the complex's connectivity, not just its dimension.

## Conclusion

- **The tower extends cleanly:** `λ₂(T₄) ≤ λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)` holds on all 198 fully-connected 4-complexes, with the Johnson anchor (λ₂ = n at every level for `K_n`) reproduced exactly.
- The new top link `λ₂(T₄) ≤ λ₂(T₃)` shows the same behaviour as its two predecessors — consistent with a **general spectral monotonicity up the simplicial ladder** (`k`-faces → `(k+1)`-faces) at every dimension, not a low-dimensional accident.
- **Decay is monotone but not uniform:** ratios stay in (0,1], equal 1 only for the densest (complete) complexes, and drop further the sparser/more-bottlenecked the complex — there is no universal constant decay factor.

## Caveats

- Exploration only: clique complexes `K_{5..9}`, ~900 random 4-complexes (needs 5-cliques, so dense), plus the `T₃`-level spheres/random complexes for `r₁,r₂`. Not a census; no proofs.
- `T(G)` uses 3-cliques of the 1-skeleton; `T₃,T₄` use `K`'s actual faces (they coincide for clique complexes). `λ₂` numerical (`eigvalsh`), tol 1e-9.

