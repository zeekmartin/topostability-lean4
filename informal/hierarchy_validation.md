# Hierarchy validation — Conjectures A & B and the 4-level chain

Tests two conjectured spectral inequalities and whether they compose into a single increasing chain.

- **Conjecture A (corrected, Paper 11 replacement):** `τ(G)/(Δ−1) ≤ λ₂(G)`.
- **Conjecture B (Paper 14):** `λ₂(T(G)) ≤ λ₂(G)` when `T(G)` is connected (proved for regular `G`; open in general).
- **4-level chain:** `τ → τ/(Δ−1) ≤ λ₂(T(G)) ≤ λ₂(G)` (the first step is normalisation; the rest is the conjectured ordering). If it holds, **A is a corollary of B plus the new link `τ/(Δ−1) ≤ λ₂(T(G))`**.

## Sample

- **n = 4..7: EXHAUSTIVE** up to isomorphism via `networkx.graph_atlas_g()`.
- **n = 8, 9: NON-exhaustive** (not in atlas; no nauty/geng) — glued cliques, complete multipartite, circulants + a dense random sweep.
  - n=4 (exhaustive): 6 connected graphs
  - n=5 (exhaustive): 21 connected graphs
  - n=6 (exhaustive): 112 connected graphs
  - n=7 (exhaustive): 853 connected graphs
  - n=8 (sampled): 42838 connected graphs
  - n=9 (sampled): 29123 connected graphs
- **Total: 72953 connected graphs** (45196 have `T(G)` connected → eligible for B and the chain).

## Conjecture A — τ/(Δ−1) ≤ λ₂(G)

✅ **HOLDS** on all 72953 applicable graphs. Tightest ratio τ/(Δ-1)/λ₂(G) = 0.7603 (`rand8` n=8 τ=1 Δ=4 λ₂(T)=n/a λ₂(G)=0.4384).

## Conjecture B — λ₂(T(G)) ≤ λ₂(G)  [T(G) connected]

✅ **HOLDS** on all 45196 applicable graphs. Tightest ratio λ₂(T)/λ₂(G) = 1.0000 (`circ8-(1, 2, 3, 4)` n=8 τ=6 Δ=7 λ₂(T)=8.0000 λ₂(G)=8.0000).

## New link — τ/(Δ−1) ≤ λ₂(T(G))

❌ **FAILS**: 421/45196 violations (421 irregular). Worst slack λ₂(T)−τ/(Δ-1) = -0.2047 (`rand8` n=8 m=15 τ=1 Δ=4 λ₂(T)=0.1286 λ₂(G)=1.7857).

## The 4-level chain  τ/(Δ−1) ≤ λ₂(T(G)) ≤ λ₂(G)

- Applicable graphs (T(G) connected, Δ≥2): **45196**.
- **Full chain holds on 44775/45196 (99.07%).**
- Link 1 `τ/(Δ−1) ≤ λ₂(T)` failures: 421.
- Link 2 `λ₂(T) ≤ λ₂(G)` failures: 0.
- ❌ The chain breaks on some graphs (see link failures above).

## Correlation matrix (Pearson)

Over the 45196 graphs where all four quantities are defined (`T(G)` connected, `Δ ≥ 2`):

| | tauG | tauG/(Δ-1) | λ₂(T(G)) | λ₂(G) |
|---|---|---|---|---|
| **tauG** | 1.000 | 0.985 | 0.960 | 0.910 |
| **tauG/(Δ-1)** | 0.985 | 1.000 | 0.944 | 0.886 |
| **λ₂(T(G))** | 0.960 | 0.944 | 1.000 | 0.962 |
| **λ₂(G)** | 0.910 | 0.886 | 0.962 | 1.000 |

## Findings

1. **Conjecture A holds** on all 72953 applicable graphs (tightest ratio 0.7603) — confirms `τ/(Δ−1) ≤ λ₂(G)`, now extended to n=8,9.
2. **Conjecture B holds** on all 45196 graphs with `T(G)` connected, including irregular ones, with equality (ratio 1.0) attained by regular graphs. Strong evidence that the Paper 14 conjecture `λ₂(T(G)) ≤ λ₂(G)` is true in general, not just the proved regular case.
3. **The chain does NOT compose.** The intermediate link `τ/(Δ−1) ≤ λ₂(T(G))` **fails** (421 violations, all irregular). So although A and B are each (empirically) true, **A is not a corollary of B**: `τ/(Δ−1)` can exceed `λ₂(T(G))` while still staying under `λ₂(G)`. The triangle-graph gap `λ₂(T(G))` is a *tighter* lower bound on `λ₂(G)` (ratio→1) than `τ/(Δ−1)` (ratio 0.76), but it does not dominate `τ/(Δ−1)`. Consequence for proofs: **A should be proved directly** (Rayleigh route), not factored through `T(G)`.
4. **Correlations** are all strongly positive (0.89–0.99). `λ₂(T(G))` is the quantity most correlated with `λ₂(G)` (r=0.962), more than `τ/(Δ−1)` (r=0.886) — consistent with B being the tighter bound.

## Caveats

- n ≤ 7 exhaustive up to iso; n = 8, 9 sampled (structured + random), not exhaustive; n ≥ 10 untested.
- `λ₂` computed numerically (`numpy.linalg.eigvalsh`), tolerance 1e-9.
- These are empirical observations, not proofs.

