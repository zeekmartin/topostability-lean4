# Corrected-inequality search (candidates for irregular graphs)

Since **`tauG ≤ λ₂` is false**, this tests normalised candidate inequalities to find which hold for *all* connected graphs (irregular included).

## Sample

- **n = 4..7: EXHAUSTIVE** up to isomorphism via `networkx.graph_atlas_g()` (the atlas contains every graph on ≤ 7 nodes).
  - n=4: 6 connected graphs
  - n=5: 21 connected graphs
  - n=6: 112 connected graphs
  - n=7: 853 connected graphs
- **n = 8: NON-exhaustive** (not in the atlas; no nauty/geng available). Structured threat families + broad random sweep: 106248 connected graphs.
- **Total graphs tested: 107240** (104791 irregular, 2449 regular).

## Candidate inequalities

| # | Inequality | Holds? | #viol (irreg) | Worst violation | Tightest / max ratio |
|---|------------|--------|---------------|-----------------|----------------------|
| 1 | tauG / Delta <= lambda2 | ✅ ALWAYS | 0 (0) | — | slack=0.1884 ratio=0.5702 [rand8 n=8 τ=1 Δ=4 δ=2 λ₂=0.4384] |
| 2 | tauG * delta / Delta <= lambda2 | ❌ FAILS | 10 (10) | slack=-0.0616 [rand8 n=8 τ=1 Δ=4 δ=2 λ₂=0.4384] | max ratio=1.1404 |
| 3 | tauG / (Delta - 1) <= lambda2 | ✅ ALWAYS | 0 (0) | — | slack=0.1051 ratio=0.7603 [rand8 n=8 τ=1 Δ=4 δ=2 λ₂=0.4384] |
| 4 | tauG <= lambda2 * n / 2 | ✅ ALWAYS | 0 (0) | — | slack=0.7538 ratio=0.5714 [rand8 n=8 τ=1 Δ=4 δ=2 λ₂=0.4384] |
| 5 | 2(tauG+1)^2 / (n^2 Delta^3) <= lambda2 | ✅ ALWAYS | 0 (0) | — | slack=0.1483 ratio=0.0267 [rand8 n=8 τ=0 Δ=2 δ=1 λ₂=0.1522] |

## Details

### 1. tauG / Delta <= lambda2

- **Holds for all 107240 graphs.** No violation.
- Tightest (smallest slack RHS−LHS = 0.188447): `rand8` n=8 m=11 τ=1 Δ=4 δ=2 λ₂=0.438447 (irregular).
- Max ratio LHS/RHS = 0.570194: `rand8` n=8 τ=1 Δ=4 δ=2 λ₂=0.438447.

### 2. tauG * delta / Delta <= lambda2

- **FAILS**: 10 violations (10 on irregular graphs).
- Worst (slack RHS−LHS = -0.061553): `rand8` n=8 m=11 τ=1 Δ=4 δ=2 λ₂=0.438447 (irregular).

### 3. tauG / (Delta - 1) <= lambda2

- **Holds for all 107240 graphs.** No violation.
- Tightest (smallest slack RHS−LHS = 0.105114): `rand8` n=8 m=11 τ=1 Δ=4 δ=2 λ₂=0.438447 (irregular).
- Max ratio LHS/RHS = 0.760259: `rand8` n=8 τ=1 Δ=4 δ=2 λ₂=0.438447.

### 4. tauG <= lambda2 * n / 2

- **Holds for all 107240 graphs.** No violation.
- Tightest (smallest slack RHS−LHS = 0.753789): `rand8` n=8 m=11 τ=1 Δ=4 δ=2 λ₂=0.438447 (irregular).
- Max ratio LHS/RHS = 0.571429: `atlas-n7` n=7 τ=2 Δ=6 δ=3 λ₂=1.000000.

### 5. 2(tauG+1)^2 / (n^2 Delta^3) <= lambda2  [Paper12 lambda2_lower_bound]

- **Holds for all 107240 graphs.** No violation.
- Tightest (smallest slack RHS−LHS = 0.148335): `rand8` n=8 m=7 τ=0 Δ=2 δ=1 λ₂=0.152241 (irregular).
- Max ratio LHS/RHS = 0.026674: `atlas-n4` n=4 τ=0 Δ=2 δ=1 λ₂=0.585786.

## Correlation: tauG/Delta vs lambda2

- All graphs (n=107240):     Pearson r = 0.9272,  Spearman ρ = 0.8872
- Irregular only (n=104791): Pearson r = 0.9113,  Spearman ρ = 0.8790

Strong positive monotone association: `tauG/Δ` tracks `λ₂` closely, consistent with a degree-normalised bound being the right form.

## Conclusion

**Recommended corrected inequality:  `tauG ≤ Δ · λ₂`**  (equivalently `tauG / Δ ≤ λ₂`).

- It holds for **all 107240 tested graphs** (exhaustive n≤7, sampled n=8), regular and irregular alike, with the binding case at ratio 0.5702 (≈ 43% margin).
- The structural reason it survives the glued-clique refutation family `K_m ∪_s K_m`: there `tauG = m−2`, `Δ ≈ 2m−s−1`, `λ₂ = s`, so `tauG/Δ ≈ (m−2)/(2m−s−1) < 1 ≤ s = λ₂` — the `Δ` normalisation absorbs the local density that broke `tauG ≤ λ₂`.
- The **tighter** `tauG ≤ (Δ−1)·λ₂` also holds on the whole tested set (binding ratio 0.7603). Since `tauG ≤ Δ−1` always (an edge's common neighbours are ≤ deg−1), this is the strongest clean variant found; it is the natural target if one wants a provable spectral lower bound `λ₂ ≥ tauG/(Δ−1)`.
- `tauG · δ / Δ ≤ λ₂` is **false** (10 irregular violations) — multiplying by the min-degree factor `δ` overshoots.
- `tauG ≤ λ₂·n/2` and the Paper 12 bound `2(tauG+1)²/(n²Δ³) ≤ λ₂` hold but are very loose (ratios 0.57 and 0.03).

**Critical binding graph** (tightest for `tauG ≤ Δ·λ₂`, also the worst violator of candidate #2): n=8, m=11, τ=1, Δ=4, δ=2, λ₂=0.438447.
Edges: `[(0, 2), (0, 6), (1, 3), (1, 5), (2, 4), (2, 6), (2, 7), (3, 5), (3, 7), (4, 7), (5, 7)]`

**Caveats.** n≤7 is exhaustive up to isomorphism; n=8 is sampled (106248 graphs, structured + random) — not exhaustive; n≥9 untested. These are empirical observations, not proofs. The recommended bound is a conjecture supported by this search, not a theorem.

