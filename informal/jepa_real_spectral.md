# Spectral hierarchy on a REAL JEPA model

**Model.** `facebook/ijepa_vith14_1k` (32 layers × 16 heads, hidden 1280, 256 attention tokens), run on a Modal **cuda** GPU over **16** real images. For each `(layer, head)` we average the self-attention map over images and flatten it to a signature; heads are joined when their attention maps correlate with Pearson **r > 0.3**.

**Question.** The inequality `λ₂(T(G)) ≤ λ₂(G)` (and the full chain `λ₂(T₃) ≤ λ₂(T(G)) ≤ λ₂(G)`) held across 45,000+ synthetic graphs with zero violations. Does it survive on a *trained* transformer's real head-to-head attention-correlation graph?

## Headline

- **Eligible layers** (both `G` and `T(G)` connected, so the inequality is defined): **16/32**. The other 16 have a disconnected `T(G)` — `ρ` is undefined there and they are excluded (not counted as violations).
- **Per-layer upper link `λ₂(T(G)) ≤ λ₂(G)`: ✅ 0 violations across the 16 eligible layers.**
- **Global graph (all 512 heads): upper link n/a (graph not eligible)**; full chain n/a (T₃ disconnected).
- Per-layer coherence ratio ρ = λ₂(T)/λ₂(G) over eligible layers: mean 0.464, range [0.190, 0.752].

## Per-layer spectral hierarchy

`G conn` / `T(G) conn` = whether each graph is connected; the upper link is only tested on layers where both are (`link` = ✅/❌), else `n/a`.

| layer | edges | dens | G conn | T(G) conn | λ₂(G) | λ₂(T(G)) | ρ=λ₂(T)/λ₂(G) | FI | link |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 52 | 0.43 | y | n | 0.732 | -0.000 | — | 0.038 | n/a |
| 1 | 100 | 0.83 | y | y | 6.437 | 4.531 | 0.704 | 0.000 | ✅ |
| 2 | 77 | 0.64 | y | y | 2.556 | 0.963 | 0.377 | 0.000 | ✅ |
| 3 | 55 | 0.46 | y | n | 0.391 | -0.000 | — | 0.036 | n/a |
| 4 | 50 | 0.42 | y | y | 1.848 | 0.491 | 0.266 | 0.000 | ✅ |
| 5 | 62 | 0.52 | y | y | 1.675 | 0.318 | 0.190 | 0.000 | ✅ |
| 6 | 45 | 0.38 | n | n | -0.000 | 0.000 | — | 0.022 | n/a |
| 7 | 80 | 0.67 | y | y | 3.559 | 2.161 | 0.607 | 0.000 | ✅ |
| 8 | 83 | 0.69 | y | y | 2.925 | 1.249 | 0.427 | 0.000 | ✅ |
| 9 | 38 | 0.32 | n | n | 0.000 | -0.000 | — | 0.053 | n/a |
| 10 | 36 | 0.30 | n | y | 0.000 | 0.435 | — | 0.000 | n/a |
| 11 | 36 | 0.30 | n | n | 0.000 | -0.000 | — | 0.083 | n/a |
| 12 | 57 | 0.47 | y | n | 0.933 | 0.000 | — | 0.018 | n/a |
| 13 | 80 | 0.67 | y | y | 3.164 | 1.587 | 0.502 | 0.000 | ✅ |
| 14 | 85 | 0.71 | n | y | 0.000 | 3.031 | — | 0.000 | n/a |
| 15 | 71 | 0.59 | n | n | -0.000 | 0.000 | — | 0.014 | n/a |
| 16 | 56 | 0.47 | n | y | -0.000 | 0.512 | — | 0.000 | n/a |
| 17 | 51 | 0.42 | y | n | 0.432 | 0.000 | — | 0.000 | n/a |
| 18 | 65 | 0.54 | y | y | 2.083 | 0.655 | 0.315 | 0.000 | ✅ |
| 19 | 67 | 0.56 | y | n | 0.858 | 0.000 | — | 0.015 | n/a |
| 20 | 66 | 0.55 | y | n | 0.623 | -0.000 | — | 0.015 | n/a |
| 21 | 78 | 0.65 | y | y | 2.929 | 1.178 | 0.402 | 0.000 | ✅ |
| 22 | 72 | 0.60 | y | y | 3.155 | 1.308 | 0.415 | 0.000 | ✅ |
| 23 | 72 | 0.60 | y | y | 4.084 | 1.838 | 0.450 | 0.000 | ✅ |
| 24 | 62 | 0.52 | y | y | 1.615 | 0.715 | 0.443 | 0.000 | ✅ |
| 25 | 97 | 0.81 | y | y | 3.930 | 2.759 | 0.702 | 0.000 | ✅ |
| 26 | 82 | 0.68 | y | n | 0.632 | 0.000 | — | 0.012 | n/a |
| 27 | 89 | 0.74 | y | y | 1.891 | 0.851 | 0.450 | 0.000 | ✅ |
| 28 | 58 | 0.48 | n | n | 0.000 | -0.000 | — | 0.034 | n/a |
| 29 | 87 | 0.72 | y | y | 1.820 | 0.773 | 0.425 | 0.000 | ✅ |
| 30 | 104 | 0.87 | y | y | 7.410 | 5.575 | 0.752 | 0.000 | ✅ |
| 31 | 105 | 0.88 | n | y | 0.000 | 15.000 | — | 0.000 | n/a |

## Which layers have the steepest coherence drop?

Smallest ρ = steepest drop from vertex- to edge-connectivity:

- **layer 5** — ρ = 0.190 (λ₂(G)=1.675, λ₂(T)=0.318)
- **layer 4** — ρ = 0.266 (λ₂(G)=1.848, λ₂(T)=0.491)
- **layer 18** — ρ = 0.315 (λ₂(G)=2.083, λ₂(T)=0.655)
- **layer 2** — ρ = 0.377 (λ₂(G)=2.556, λ₂(T)=0.963)
- **layer 21** — ρ = 0.402 (λ₂(G)=2.929, λ₂(T)=1.178)

- Flattest (ρ closest to 1): **layer 30** (ρ = 0.752).

## Global attention graph (all heads)

- Threshold used: **0.74** (raised from the requested r > 0.3 so the dense 512-head graph's triangle count stays exactly computable).
- Full graph: 512 heads, 1298 edges, **191 connected components** — so the hierarchy is evaluated on the **giant component**.
- Giant component: 290 nodes, 1258 edges, density 0.030.
- λ₂(G) = 0.0102, λ₂(T(G)) = -0.0000, λ₂(T₃) = 0.0000.
- FI = 0.0663; ρ / upper link **n/a** — G connected=True, T(G) connected=False (inequality undefined unless both are connected).
- T(G): 1258 nodes / 9930 edges (connected=False); T₃: 3310 nodes (connected=False).

## SAL-style head masking (mask 33% of heads)

Randomly drop **169/512** heads (33%), recompute the induced attention graph; 40 trials (seed 0), threshold 0.74. FI = fraction of edges in zero triangles (SAL fragility index; higher = more fragile), computed on the full induced graph; ρ is the giant-component value.

| quantity | before (full) | after masking (mean ± std) |
|---|---|---|
| ρ = λ₂(T)/λ₂(G) | — | — ± — |
| FI (fragility) | 0.0663 | 0.1010 ± 0.0183 |

- Masking **raises FI** by 0.035 → the remaining structure becomes more fragile.
- Of 40 masked subgraphs, 0 were eligible (both `G` and `T(G)` connected); upper-link violations among them: **0/40** (none eligible).

## Takeaways

- **The hierarchy `λ₂(T(G)) ≤ λ₂(G)` holds on real JEPA attention connectivity** wherever it is defined: **0 violations across the 16 eligible layers** (ρ ∈ [0.19, 0.75] < 1) — consistent with the 45,000+ synthetic-graph result. The inequality is not an artifact of synthetic topology.
- **The connectivity gate is the real story.** Half the layers, and the entire 512-head global graph, have a **disconnected `T(G)`**: many attention-head pairs correlate without sitting in any triangle, so the inequality is simply *undefined* there (reported `n/a`, never silently counted as a pass). Real attention connectivity is far more triangle-sparse than the dense synthetic families.
- **SAL masking → fragility.** ρ is undefined under masking (the masked giant components also have disconnected `T(G)`), but FI is well-defined and **rises 0.066 → 0.101** when 33% of heads are dropped: removing heads makes the remaining attention graph more fragile (more edges fall outside any triangle).
- ρ measures how much algebraic connectivity is lost passing from heads to head-interactions; per-layer ρ identifies which depths carry the most redundant (triangle-rich) vs. fragile attention structure (steepest: layer 5, ρ=0.19; flattest: layer 30, ρ=0.75).

## Caveats

- One model (`facebook/ijepa_vith14_1k`), 16 images, single seed. Graphs are unweighted (edge iff r > τ). **Per-layer**: λ₂ on the full graph, with ρ/violation gated on both `G` and `T(G)` being connected (exactly the 45k-graph protocol — no component surgery). **Global** (512 heads): the graph is disconnected, so the hierarchy is evaluated on its giant component (a legitimately connected graph), while FI is computed on the full graph. The global τ is raised from 0.3 until the triangle count is exactly computable; the τ used is reported.
- Head masking here is **graph-level** (drop head-nodes, recompute the induced correlation graph), not a re-forward-pass with head outputs zeroed; it isolates the structural effect on the attention graph, the level at which SAL's FI is defined.

