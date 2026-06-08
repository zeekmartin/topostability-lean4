# Structural analysis of the 421 link-violation graphs

The **link violations** are the connected graphs with `T(G)` connected, `Δ ≥ 2`, and

> **`τ(G)/(Δ−1) > λ₂(T(G))`**

i.e. the normalised *local* triangle support exceeds the *global* triangle connectivity (the spectral gap of the triangle graph). They are exactly the graphs where Conjecture A is **not** explained by Conjecture B (see [`hierarchy_validation.md`](hierarchy_validation.md)). All 421 are irregular; both A (`τ/(Δ−1) ≤ λ₂(G)`) and B (`λ₂(T(G)) ≤ λ₂(G)`) still hold on every one of them — only the *link* between them breaks.

- Recovered **421** violators (deterministic regeneration of the same dataset).
- Vertex-count distribution: n=7: 5, n=8: 258, n=9: 158.

## Metric definitions

- `κ`, `κ'` = vertex / edge connectivity of `G`; `artic`, `bridges` = number of articulation points / bridges of `G`.
- `weak_comp` = number of connected components of `T(G)` after deleting the weakest 10% of its edges, where an edge's weight is the Jaccard embeddedness of its endpoints in `T(G)` (low = inter-module 'weak tie').
- `modularity`, `ncomm` = greedy-modularity value and community count of `T(G)`.
- `tri(e)` = number of triangles on edge `e` (= common neighbours); `tri_cv` = coefficient of variation (std/mean) over edges.
- `PRnorm` = participation ratio of `T(G)`'s Fiedler vector (eigenvector of λ₂(T(G))), in (0,1]; low = localised bottleneck. *(Operational reading of the Paper-14 PRnorm — no formal definition exists in the repo.)*
- `diameter`, `avg_path`, `clustering` = of `G`.

## Aggregate statistics (min / median / mean / max)

| metric | min | median | mean | max |
|---|---|---|---|---|
| `n` | 7.000 | 8.000 | 8.363 | 9.000 |
| `m` | 11.000 | 17.000 | 17.012 | 23.000 |
| `Delta` | 4.000 | 5.000 | 5.432 | 7.000 |
| `delta` | 2.000 | 3.000 | 2.637 | 4.000 |
| `tau` | 1.000 | 1.000 | 1.000 | 1.000 |
| `l2G` | 0.698 | 1.885 | 1.800 | 3.330 |
| `l2T` | 0.092 | 0.174 | 0.174 | 0.250 |
| `lo` | 0.167 | 0.250 | 0.229 | 0.333 |
| `slack` | -0.205 | -0.052 | -0.055 | -0.000 |
| `kappa` | 2.000 | 3.000 | 2.613 | 4.000 |
| `kappa_e` | 2.000 | 3.000 | 2.637 | 4.000 |
| `artic` | 0.000 | 0.000 | 0.000 | 0.000 |
| `bridges` | 0.000 | 0.000 | 0.000 | 0.000 |
| `modularity` | 0.307 | 0.434 | 0.431 | 0.540 |
| `ncomm` | 2.000 | 3.000 | 3.397 | 5.000 |
| `weak_comp` | 1.000 | 1.000 | 1.285 | 3.000 |
| `tri_max` | 2.000 | 3.000 | 2.931 | 5.000 |
| `tri_cv` | 0.273 | 0.404 | 0.392 | 0.533 |
| `PRnorm` | 0.298 | 0.580 | 0.579 | 0.857 |
| `diameter` | 2.000 | 2.000 | 2.423 | 4.000 |
| `avg_path` | 1.333 | 1.444 | 1.479 | 1.833 |
| `clustering` | 0.426 | 0.570 | 0.578 | 0.763 |

## Key question — one structural motif for ALL violations?

Hypothesis (from review): *"dense modules weakly connected by few triangles"*. To see whether a signature is **discriminating** (not merely common), each is measured on the **421 violators** and on a matched sample of **1493 non-violators** (graphs where the link holds).

| Structural signature | Violators | Non-violators | Discriminating? |
|---|---|---|---|
| T(G) modularity ≥ 0.30 | **100.0%** | 18.3% | ✅ strong (+82 pts) |
| weak-tie removal disconnects T(G) (weak_comp ≥ 2) | **27.3%** | 20.4% | ✗ no (+7 pts) |
| T(G) communities ≥ 2 | **100.0%** | 100.0% | ✗ no (+0 pts) |
| localised Fiedler vector (PRnorm ≤ 0.5) | **28.3%** | 83.1% | ✅ strong (-55 pts) |
| uneven triangle counts (tri_cv ≥ 0.5) | **1.7%** | 0.7% | ✗ no (+1 pts) |
| G low vertex-connectivity (κ ≤ 2) | **40.6%** | 9.6% | ✅ strong (+31 pts) |
| G has an articulation point | **0.0%** | 0.0% | ✗ no (+0 pts) |
| G has a bridge | **0.0%** | 0.0% | ✗ no (+0 pts) |
| JOINT: modularity ≥ 0.30 AND weak_comp ≥ 2 | **27.3%** | 2.4% | • mild (+25 pts) |

**Three facts hold for ALL 421 violators:**
1. **`τ(G) = 1`** — every violator has a weakest edge in *exactly one* triangle (100%; vs 34% of non-violators). So violations are a `τ=1` phenomenon: `τ/(Δ−1) = 1/(Δ−1)` just has to clear a small `λ₂(T(G))`.
2. **`T(G)` is modular** — modularity ≥ 0.31 on **100%** of violators vs only 18% of non-violators (the *"dense modules"* half of the hypothesis is universal **and** discriminating).
3. **`G` is never articulated** — articulation points / bridges on **0%** (κ ≥ 2 always; κ ≤ 2 on 41%). The weakness is **not** at the graph level; `G` itself is well-connected.

➡️ **Refined answer — a single necessary motif, sharply located.** Every violator is a **`τ=1`, 2-connected graph whose triangle graph `T(G)` is modular** (modularity ≥ 0.31, 100% vs 18% of non-violators). The *"dense modules"* half of the hypothesis is universal and strongly discriminating; the *"weakly connected by few triangles"* half appears in a **strong form** (`T(G)` fragments under weak-tie removal) for ~27% and a mild form for the rest. The decisive correction to the hypothesis: the bottleneck lives **entirely inside `T(G)`** — dense triangle communities joined by few triangles depress `λ₂(T(G))` below the locally-supported `τ/(Δ−1)=1/(Δ−1)` — while `G` itself stays well-connected (0% articulation points, κ ≥ 2). So: *correct in spirit, but the modules and their weak coupling are in the **triangle graph**, not in `G`, and the trigger is always a single-triangle edge.*

## Clusters (k-means, best of k∈{3,4,5} by silhouette → k=4, silhouette=0.201)

Cluster means of the key descriptors:

| cluster | size | `n` | `m` | `Delta` | `tau` | `l2G` | `l2T` | `slack` | `kappa` | `artic` | `bridges` | `modularity` | `ncomm` | `weak_comp` | `tri_cv` | `PRnorm` | `clustering` | `avg_path` |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 0 | 69 | 8.20 | 14.41 | 5.20 | 1.00 | 0.98 | 0.21 | -0.03 | 2.00 | 0.00 | 0.00 | 0.42 | 3.26 | 1.14 | 0.37 | 0.60 | 0.68 | 1.64 |
| 1 | 130 | 8.09 | 16.86 | 5.01 | 1.00 | 2.15 | 0.18 | -0.07 | 3.04 | 0.00 | 0.00 | 0.42 | 3.32 | 1.26 | 0.39 | 0.56 | 0.55 | 1.42 |
| 2 | 131 | 8.69 | 18.89 | 6.06 | 1.00 | 2.07 | 0.17 | -0.03 | 2.92 | 0.00 | 0.00 | 0.42 | 3.40 | 1.42 | 0.40 | 0.54 | 0.56 | 1.44 |
| 3 | 91 | 8.40 | 16.49 | 5.31 | 1.00 | 1.53 | 0.15 | -0.08 | 2.03 | 0.00 | 0.00 | 0.46 | 3.59 | 1.23 | 0.40 | 0.63 | 0.57 | 1.51 |

### Cluster descriptions

- **Cluster 0** (69 graphs): high `avg_path`, low `l2G`, high `clustering`, low `m`. Mean n=8.2, modularity=0.42, slack=-0.031.
- **Cluster 1** (130 graphs): high `kappa`, low `Delta`, high `l2G`, low `avg_path`. Mean n=8.1, modularity=0.42, slack=-0.071.
- **Cluster 2** (131 graphs): high `Delta`, high `m`, high `n`, high `slack`. Mean n=8.7, modularity=0.42, slack=-0.032.
- **Cluster 3** (91 graphs): low `kappa`, high `modularity`, low `slack`, low `l2T`. Mean n=8.4, modularity=0.46, slack=-0.082.

## The 5 most extreme violations (most negative slack λ₂(T)−τ/(Δ−1))

### V1 — slack -0.2047  (`rand8`, cluster 1)

- n=8, m=15, Δ=4, δ=3, τ=1; **τ/(Δ−1)=0.3333 > λ₂(T(G))=0.1286**, λ₂(G)=1.7857 (A still holds: 0.3333 ≤ 1.7857).
- κ=3, κ'=3, artic=0, bridges=0; T(G): 15v/21e, modularity=0.463, communities=4, weak_comp=1, PRnorm=0.668.
- triangle dist: max=2, min=1, mean=1.40, cv=0.350; diam=2, avg_path=1.46, clustering=0.521.
- edges: `[(0, 2), (0, 4), (0, 5), (0, 7), (1, 2), (1, 3), (1, 6), (1, 7), (2, 5), (2, 6), (3, 4), (3, 6), (3, 7), (4, 7), (5, 6)]`

### V2 — slack -0.1633  (`atlas-n7`, cluster 1)

- n=7, m=13, Δ=4, δ=3, τ=1; **τ/(Δ−1)=0.3333 > λ₂(T(G))=0.1700**, λ₂(G)=2.1206 (A still holds: 0.3333 ≤ 2.1206).
- κ=3, κ'=3, artic=0, bridges=0; T(G): 13v/18e, modularity=0.420, communities=3, weak_comp=1, PRnorm=0.669.
- triangle dist: max=2, min=1, mean=1.38, cv=0.351; diam=2, avg_path=1.38, clustering=0.524.
- edges: `[(0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 6), (2, 3), (2, 5), (2, 6), (3, 4), (3, 5), (4, 5), (4, 6)]`

### V3 — slack -0.1578  (`rand9`, cluster 1)

- n=9, m=20, Δ=5, δ=3, τ=1; **τ/(Δ−1)=0.2500 > λ₂(T(G))=0.0922**, λ₂(G)=2.3554 (A still holds: 0.2500 ≤ 2.3554).
- κ=3, κ'=3, artic=0, bridges=0; T(G): 20v/33e, modularity=0.496, communities=3, weak_comp=1, PRnorm=0.740.
- triangle dist: max=3, min=1, mean=1.65, cv=0.440; diam=2, avg_path=1.44, clustering=0.485.
- edges: `[(0, 1), (0, 3), (0, 8), (1, 3), (1, 4), (1, 5), (1, 7), (2, 4), (2, 5), (2, 6), (2, 8), (3, 4), (3, 6), (3, 8), (4, 5), (4, 7), (5, 7), (6, 7), (6, 8), (7, 8)]`

### V4 — slack -0.1494  (`rand9`, cluster 3)

- n=9, m=17, Δ=5, δ=2, τ=1; **τ/(Δ−1)=0.2500 > λ₂(T(G))=0.1006**, λ₂(G)=1.3862 (A still holds: 0.2500 ≤ 1.3862).
- κ=2, κ'=2, artic=0, bridges=0; T(G): 17v/24e, modularity=0.500, communities=3, weak_comp=1, PRnorm=0.668.
- triangle dist: max=2, min=1, mean=1.41, cv=0.349; diam=3, avg_path=1.58, clustering=0.567.
- edges: `[(0, 1), (0, 2), (0, 3), (0, 5), (0, 6), (1, 2), (1, 6), (2, 3), (2, 4), (2, 8), (3, 4), (4, 7), (4, 8), (5, 6), (5, 8), (6, 8), (7, 8)]`

### V5 — slack -0.1403  (`rand9`, cluster 1)

- n=9, m=20, Δ=5, δ=4, τ=1; **τ/(Δ−1)=0.2500 > λ₂(T(G))=0.1097**, λ₂(G)=2.5210 (A still holds: 0.2500 ≤ 2.5210).
- κ=4, κ'=4, artic=0, bridges=0; T(G): 20v/30e, modularity=0.540, communities=4, weak_comp=2, PRnorm=0.680.
- triangle dist: max=3, min=1, mean=1.50, cv=0.447; diam=2, avg_path=1.44, clustering=0.437.
- edges: `[(0, 4), (0, 5), (0, 6), (0, 8), (1, 2), (1, 3), (1, 4), (1, 7), (1, 8), (2, 3), (2, 4), (2, 7), (3, 5), (3, 6), (4, 6), (4, 8), (5, 6), (5, 7), (5, 8), (6, 7)]`

## Caveats

- The 421 come from a dataset that is exhaustive only for n ≤ 7; n=8,9 are sampled, so the violator set is a representative sample, not a census.
- `PRnorm` and the weak-tie removal are operational definitions (stated above), chosen to probe the hypothesis; no formal Paper-14 definitions exist in the repo.
- **`PRnorm` caveat:** for dense/symmetric `T(G)` (mostly non-violators) `λ₂(T(G))` is often *degenerate* (high multiplicity), so `eigh`'s chosen Fiedler vector is an arbitrary, often-localised basis vector — the non-violator `PRnorm` column is therefore not fully meaningful. The violator side (simple, small `λ₂(T)`) is reliable. The robust discriminator is **`T(G)` modularity**, not `PRnorm`.
- All quantities numerical (`eigvalsh`), tolerance 1e-9. Empirical, not proofs.

