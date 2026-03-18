# Topostability — Lean 4 Formalization

**Author**: David Martin Venti (Zeek)  
**ORCID**: 0009-0000-6675-7821  
**Affiliation**: Cognitive Engineering, Switzerland  
**Repository**: https://github.com/zeekmartin/topostability-lean4

## Overview

Formal verification in Lean 4 (Mathlib4) of spectral graph theory results
from the Topostability research programme (Papers 11–13).
All theorems are **sorry-free** and verified against standard Lean 4 axioms
only (`propext`, `Classical.choice`, `Quot.sound`).

## Files

| File | Contents |
|------|----------|
| `Defs.lean` | Core definitions: `triCount`, `tauG`, `totalTriangles`, `fragilityIndex`, `triangleGraph`, `edgeLift` |
| `Conjectures.lean` | All proofs: spectral identity, Cheeger inequality, lower/upper bounds, Paper 13 main theorem |
| `Verify.lean` | Computational verification on K3, K4, P3, C4 |
| `Tests.lean` | Axiom checks and type-level sanity tests |

## Proved Theorems (~35 total)

### Paper 12 — Lower bound via τ(G)
| Lean name | Statement |
|-----------|-----------|
| `cut_multiplication` | τ(G) ≥ k → every cut has ≥ k+1 edges |
| `conductance_lower_bound` | h(G) ≥ 2(τ+1)/(nΔ) |
| `cheeger_inequality` | h(G)²/(2Δ) ≤ λ₂(L) |
| `lambda2_lower_bound` | λ₂(L) ≥ 2(τ(G)+1)²/(n²Δ³) |

### Paper 11 — Spectral identity and upper bound
| Lean name | Statement |
|-----------|-----------|
| `spectral_identity` | tr(L·A²) = Σdᵢ² − 6T |
| `lambda2_upper_bound_regular` | λ₂(L) ≤ (nd² − 6T)/(d(n−d)) for d-regular G |

### Paper 13 — Triangle graph spectral dominance
| Lean name | Statement |
|-----------|-----------|
| `triangleGraph` (Defs.lean) | Definition of T(G) on G.edgeSet |
| `edgeLift_mk` | edgeLift G f ⟨s(u,v),h⟩ = f(u) + f(v) |
| `edgeLift_sum_zero` | ∑ h = 0 when ∑ f = 0 (d-regular) |
| `edgeLift_norm_fiedler` | ‖h‖² = (2d − λ₂)‖f‖² |
| `triangleGraph_quadratic_form` | h⊤L_{T(G)}h = Σ_{triangles} (f(v)−f(w))² |
| `triangleGraph_quadratic_bound` | h⊤L_{T(G)}h ≤ 2(d−1)·Energy_G(f) |
| `lambda2_triangle_graph_le` | **λ₂(T(G)) ≤ λ₂(G)** for connected d-regular G |

## Papers

| Paper | Topic | Zenodo DOI | Lean status |
|-------|-------|------------|-------------|
| 11 | Spectral identity + λ₂ upper bound | [10.5281/zenodo.18998719](https://doi.org/10.5281/zenodo.18998719) | ✅ Fully proved |
| 12 | τ(G) lower bound via Cheeger | [10.5281/zenodo.18998928](https://doi.org/10.5281/zenodo.18998928) | ✅ Fully proved |
| 13 | λ₂(T(G)) ≤ λ₂(G) for regular graphs | [10.5281/zenodo.18999097](https://doi.org/10.5281/zenodo.18999097) | ✅ Fully proved |
| 14 | T(G) conjecture (general graphs) | [10.5281/zenodo.19018598](https://doi.org/10.5281/zenodo.19018598) | 📖 Open (regular case proved) |

## Open Problems

- `conjecture_tauG_le_algebraicConnectivity`: τ(G) ≤ λ₂(G) — open conjecture (Paper 11)
- `sweep_pigeonhole`: technical lemma for Cheeger sweep argument
- `lambda2_triangle_graph_le` (general case): λ₂(T(G)) ≤ λ₂(G) for non-regular graphs (Paper 14)

## Axiom Verification

All proved theorems depend only on standard Lean 4 foundations:
```
propext, Classical.choice, Quot.sound
```
Verified via `#print axioms` in `Tests.lean`.

## Requirements

- Lean 4 (leanprover/lean4)
- Mathlib4 (leanprover-community/mathlib4)

## Citation

```bibtex
@misc{Venti2026lean,
  author = {Venti, David Martin},
  title  = {Topostability: Lean 4 formalization of spectral graph theory results},
  year   = {2026},
  url    = {https://github.com/zeekmartin/topostability-lean4}
}
```
