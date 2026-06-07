# Plan — prove the **corrected** conjecture: `τ(G)/(Δ−1) ≤ λ₂(G)`

## Status of the original conjecture (resolved)

The original Paper 11 Conjecture 1, `τ(G) ≤ λ₂(G)`, is **FALSE** — refuted and
documented in [`conjecture_tauG_le_lambda2_REFUTED.md`](conjecture_tauG_le_lambda2_REFUTED.md).
It fails first at `n = 6` and by an unbounded margin for glued cliques
`K_m ∪_s K_m` (`τ = m−2`, `λ₂ ≤ κ_v = s`). The `sorry` in
`conjecture_tauG_le_algebraicConnectivity` was removed; the repo is now
**100% sorry-free**. The only salvaged true fragment is the `τ = 0` sub-case
(`tauG_le_algebraicConnectivity_of_tauG_eq_zero`).

## New target

```
τ(G) / (Δ − 1) ≤ λ₂(G)        equivalently        τ(G) ≤ (Δ − 1) · λ₂(G)
```
where `τ(G) = tauG G` (min common-neighbour count over edges), `Δ = G.maxDegree`,
and `λ₂(G) = algebraicConnectivity G` (second-smallest Laplacian eigenvalue).

For `Δ = 1` (a single edge, `n = 2`) the statement is vacuous/degenerate; state it
for `Δ ≥ 2` (automatic for any connected graph on `≥ 3` vertices).

## Evidence (why this is the right inequality)

From [`corrected_conjecture_search.md`](corrected_conjecture_search.md) — `counterexample_search.py::corrected_search()`
tested 5 candidate normalisations over **107,240 connected graphs** (n = 4..7
EXHAUSTIVE up to iso via `networkx.graph_atlas_g()`; n = 8 sampled, structured +
random):

| Candidate | Result |
|-----------|--------|
| `τ/Δ ≤ λ₂` | holds on all (binding ratio 0.57) |
| **`τ/(Δ−1) ≤ λ₂`** | **holds on all (binding ratio 0.76) — tightest clean variant** |
| `τ·δ/Δ ≤ λ₂` | FALSE (10 irregular violations) |
| `τ ≤ λ₂·n/2` | holds, loose (0.57) |
| `2(τ+1)²/(n²Δ³) ≤ λ₂` (Paper 12) | holds, very loose (0.03) |

Pearson `r(τ/Δ, λ₂) = 0.93`, Spearman `ρ = 0.89`. The binding graph is `n = 8,
τ = 1, Δ = 4, λ₂ ≈ 0.438` (edges in the search writeup). **Caveat:** n ≤ 7 is
exhaustive, n = 8 sampled, n ≥ 9 untested — this is a conjecture, not a theorem.

Structural sanity on the refutation family: for `K_m ∪_s K_m`, `τ = m−2`,
`Δ = 2m−s−1`, `λ₂ = s`, so `τ/(Δ−1) = (m−2)/(2m−s−2) < 1 ≤ s` — comfortably holds.

The trivial structural half is already true: **`τ(G) ≤ Δ − 1`** always (the common
neighbours of an edge `(u,v)` are ⊆ `N(u) \ {v}`, so `≤ deg(u) − 1 ≤ Δ − 1`).
Hence `τ/(Δ−1) ≤ 1`, and the whole content is the spectral lower bound
`λ₂ ≥ τ/(Δ−1)`, i.e. **`λ₂` is bounded below by the normalised min triangle-degree.**

## Proof route — Rayleigh / Cheeger lower bound on λ₂

Goal restated: `λ₂(G) ≥ τ(G)/(Δ−1)`. Two candidate engines:

### Route R — direct Rayleigh quotient
`λ₂ = min_{x ⟂ 1, x ≠ 0} (xᵀ L x)/(xᵀ x)` with `xᵀ L x = Σ_{(u,v)∈E} (x_u − x_v)²`.
Need: for every `x ⟂ 1`, `Σ_E (x_u − x_v)² ≥ (τ/(Δ−1)) · Σ_v x_v²`. The mechanism:
each edge sits in ≥ τ triangles, and triangle/common-neighbour structure forces
enough edge-variation. The `Δ−1` denominator should appear from bounding how many
triangles share a vertex (each vertex is in ≤ `C(Δ,2)` triangles; per-edge it is
`≤ Δ−1`). This is the genuinely novel analytic core.

### Route C — via the existing discrete Cheeger machinery (Paper 12)
Paper 12 already gives `λ₂ ≥ h(G)²/(2Δ)` (`cheeger_inequality`) and
`h(G) ≥ 2(τ+1)/(nΔ)` (`conductance_lower_bound`). That chain yields only the very
weak `2(τ+1)²/(n²Δ³) ≤ λ₂` (the n-dependence kills it). To reach `τ/(Δ−1)` one needs
a **dimension-free** conductance bound `h(G) ≥ f(τ, Δ)` with no `n`, then Cheeger.
Whether such an `h`-bound holds is itself open — check small cases first.

Route R is more promising (no lossy `n` factor). Start there.

## Recommended order

1. **Lean scaffold.** State `theorem tauG_le_maxDegree_sub_one : τ(G) ≤ Δ − 1`
   (easy, true, useful lemma) and the target
   `theorem algebraicConnectivity_ge_tauG_div : (τ(G):ℝ)/(Δ−1) ≤ λ₂` as the goal.
2. **Reuse Rayleigh API.** Paper 12 / Shared already have
   `algebraicConnectivity_le_rayleigh` (λ₂ ≤ Rayleigh) and the edge-sum form of
   `xᵀ L x` (`quadratic_form_eq_edge_sum`, `bilinear_edge_sum`). A LOWER bound on λ₂
   needs the **Fiedler vector** characterisation (min over `x ⟂ 1`); locate or build
   `algebraicConnectivity = ⨅ Rayleigh over ⟂1` (the ≥ direction).
3. **Combinatorial core.** Prove `Σ_E (x_u−x_v)² ≥ (τ/(Δ−1)) Σ x²` for `x ⟂ 1`.
   Develop as Modal-verified sub-lemmas, one at a time (same loop as the Cheeger
   sweep proof). Expect this to be the bulk of the work.
4. If Route R stalls, fall back to probing Route C numerically (does a dimension-free
   `h(G) ≥ g(τ,Δ)` hold? extend `counterexample_search.py`).

## Workflow reminder

Modal loop, same as the Cheeger proof. **CLI unicode trap:** PowerShell 5.1 mangles
`≤`/`≥` passed as `--code` to `modal run` → use the `check_file` function in
`modal_lean.py` (`modal volume put <utf8 file> .../_scratch_modal.lean`, then
`modal run modal_lean.py::check_file`). API gotchas recorded in repo memory.
