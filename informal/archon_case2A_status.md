# Conjecture B — Case 2A (vertex bottleneck) status: resolvent + CF block gap

Status review of Case 2A in the three-case architecture. **Result: the Lean *bridge* is sorry-free and
reduces Case 2A (`typeA_slack_ge_required`) to a single scalar condition
`(δ−1)·D_port + maxt_core·D_core ≤ RHS` (the `hcond` of `triEnergy_le_of_partition`, validated 19/19,
margin 0.935). The resolvent + CF-block-gap mechanism is the right structure — the core gap is large
(`γ/λ ≥ 7.4`) and the exact resolvent reproduces `D_core` to machine precision — and it CLOSES cleanly
for twin-port (ratio 0.63–0.68). BUT the `γ`-resolvent UPPER BOUND `D_core ≤ γ/(γ−λ)²·‖source‖²`
overshoots the actual `D_core` by 1.4–2× on deg2+dense (the port-boundary source is spread across core
modes, not concentrated at `γ`), so the closure is only 9/17 (max 1.167). The actual inequality holds
with margin; the resolvent bound is too loose to prove it on deg2+dense.** Code:
[`archon_case2A_status.py`](../archon_case2A_status.py).

## TASK 1 — current Lean state of Case 2A

| component | location | status |
|---|---|---|
| `triEnergy_le_block_dirichlet` (`T ≤ W·D_block`, term-by-term) | `ConjectureB.lean:602` | **sorry-free** |
| `triEnergy_le_of_partition` (split + per-class ⇒ `T ≤ B` given `hcond`) | `:981` | **sorry-free** |
| `aggregate_typeA_assembly` / `aggregate_triangle_poincare_typeA` | `:950,:960` | **sorry-free** |
| `typeA_slack_ge_required` (`required ≤ aggregateSlack`) | `:1034` | **SORRY (Case 2A)** |
| `typeA_extremality_gap_nonneg`, `gapEnergy_nonneg` (dispatch) | `:1043,:1055` | sorry-free modulo above |
| Case 2B: `typeB_triEnergy_bound` (`T ≤ W·Cflat·λ₂²`) | `:634` | **sorry-free** (cond. `poincare_on_block`) |

> **Case 2A reduces to one open scalar inequality.** The bridge (`triEnergy_le_of_partition`) is
> sorry-free: given per-class triangle-count bounds (`Cp = δ−1` ports, `Cc = maxt_core` core) and the
> scalar `hcond : Cp·D_port + Cc·D_core ≤ B`, it proves `triEnergy ≤ B`. The only open content of Case 2A
> is `hcond`. Case 2B is already sorry-free (conditional on the block-flatness output `poincare_on_block`).

## TASK 2 — resolvent + CF block gap (numerical)

Core block `H` (= non-ports), gap `γ = λ₂(L_H)`; the Fiedler restricted to `H` solves
`(L_H − λ)f_H = source` where `source_v = (λ − d_v^P)f_v + Σ_{u∼v, u∈P}f_u` (port boundary, supported on
core vertices adjacent to ports). Resolvent on `1_H^⊥`: `D_core = Σ_k μ_k/(μ_k−λ)²⟨source,φ_k⟩²`.

| | result |
|---|---|
| exact resolvent `D_core` vs actual | **err 4·10⁻¹⁶** (identity confirmed) |
| CF block gap `γ/λ` | **≥ 7.4** (dense core, large gap) |
| `γ`-bound tightness `D_core / [γ/(γ−λ)²‖source‖²]` | 0.50–0.73 (deg2dense), **1.00 (twin)** |

**Closure** `2[(δ−1)D_port + maxt_core·res_bound] ≤ RHS`:

| graph | actual `T/RHS` | `γ`-bound / RHS | `λ_max`-bound / RHS | `γ/λ` |
|---|---|---|---|---|
| twin-port `K₈₀` d2 | 0.50 | **0.68** | 0.68 | 78.7 |
| twin-port `K₅₀` d3 | 0.49 | **0.63** | 0.63 | 38.4 |
| deg2+dense(80,.6) | 0.75 | **1.01** | 1.36 | 18.6 |
| deg2+dense(40,.6) | 0.71 | **1.17** | 2.00 | 7.7 |

> **`γ`-resolvent closes 9/17 (twin all, deg2dense fails at ≤ 1.167); `λ_max`-resolvent 9/17 (worse).**
> The resolvent works for **twin** (source concentrated in the `γ`-mode → bound tight, ratio 1.00) but
> overshoots for **deg2+dense** (source spread across core modes → `γ/(γ−λ)²` worst-case bound is
> 1.4–2× the true `D_core`). The actual scalar condition holds (`T/RHS ≤ 0.867`), so the inequality is
> true with margin — the *resolvent upper bound*, not the inequality, fails.

## TASK 3 — minimal Lean statement for Case 2A

> **`hcond : (δ−1)·D_port + maxt_core·D_core ≤ RHS`** — already the hypothesis of the sorry-free
> `triEnergy_le_of_partition`. Discharging it proves `typeA_slack_ge_required`. Two routes to `hcond`:
> 1. **Resolvent (CF block gap):** `D_core ≤ γ/(γ−λ)²·‖source‖²` with `γ = λ₂(L_H)`. Clean and
>    Lean-shaped (a block Courant-Fischer + resolvent norm), but **only sufficient for twin** (deg2dense
>    needs a source-spread-aware bound).
> 2. **Direct port-mass:** `D_port` and `D_core` against `RHS = Θ(λ·degQuad)`; holds 19/19 but needs the
>    Fiedler port concentration (no clean closed bound yet).

## TASK 4 — what's needed to close `triEnergy_le_RHS_exists` via three cases

`triEnergy_le_RHS_exists` (the lift bound, regime ii) dispatches as:

- **Case 1** (`Required ≤ 0`, ~97%): the aggregate `T ≤ 2λ·degQuad` (the standing aggregate sorry —
  *out of scope here*).
- **Case 2A** (`Required > 0`, vertex bottleneck): the scalar `hcond` above. **Open.** The resolvent
  closes twin but not deg2dense; needs a tighter `D_core` bound (source-spread / mode-by-mode) or the
  direct port-mass concentration.
- **Case 2B** (`Required > 0`, path bottleneck): `typeB_triEnergy_bound` (`T = O(λ₂²) ≪ RHS = Θ(λ₂)`) —
  **sorry-free** given `poincare_on_block` (block flatness, `Paper16`).

> **Needed:** (i) a Lean `poincare_on_block` instance for Case 2B's `hflat` (block resolvent flatness —
> `Paper16` machinery); (ii) for Case 2A, a `D_core` bound that closes deg2dense — the `γ`-resolvent is
> too crude (1.4–2× loss); a source-spread-aware resolvent (mode-by-mode `Σμ_k/(μ_k−λ)²`) is exact but
> not yet a closed Lean bound. Case 1 remains the aggregate (separate track).

## Conclusion

- **Case 2A is one scalar inequality** (`hcond`, sorry-free bridge); the resolvent + CF block gap is the
  right mechanism (`γ/λ ≥ 7.4`, exact `D_core` reproduced).
- **Resolvent closes twin (0.63–0.68) but not deg2dense (≤ 1.167)** — the `γ`-bound overshoots the true
  `D_core` 1.4–2× because the port-boundary source spreads over core modes.
- **The inequality itself holds 19/19** (margin 0.935 / `T/RHS ≤ 0.867`) — only the resolvent *bound* is
  too loose; a source-spread-aware bound would close it.
- **To finish via three cases:** Case 2B needs the `poincare_on_block` instance; Case 2A needs a tighter
  `D_core` bound; Case 1 is the aggregate.

## Lean
No code change (status review). Case 2A = `typeA_slack_ge_required` (sorry) reduces, via the sorry-free
`triEnergy_le_of_partition`, to the scalar `hcond`; the resolvent route is Lean-shaped but only closes
twin. 3 sorrys unchanged.
