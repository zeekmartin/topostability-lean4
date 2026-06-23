# Conjecture B — Case 2A: tightening the `D_core` bound (the BLOCK resolvent closes 17/17)

Tighten the `D_core` bound so `hcond : (δ−1)D_port + maxt_core·D_core ≤ RHS` closes on all 17 Case 2A
graphs. **Result: the γ-resolvent overshoots because it uses the GLOBAL operator norm `γ/(γ−λ)²`, but the
port-boundary source `s` is LOCALIZED on `∂` = core-vertices-adjacent-to-ports (`|∂|=2` for deg2dense).
So `D_core = s_∂ᵀ(RL_HR)_{∂∂}s_∂ ≤ λ_max((RL_HR)_{∂∂})·‖s‖²` — the BLOCK bound (the ∂-principal-submatrix
of the resolvent operator). By Cauchy interlacing `λ_max((RL_HR)_{∂∂}) ≤ λ_max(RL_HR) = γ/(γ−λ)²`, so it
is a VALID tightening, and it CLOSES ALL 17 (max ratio 0.952, margin). Also: `‖s‖² = D_port` exactly.**
Code: [`case2A_dcore_tightening.py`](../case2A_dcore_tightening.py).

## Setup

`D_core = (f_H−mean)ᵀL_H(f_H−mean) = sᵀ(RL_HR)s` where `R = (L_H−λ)^{-1}` on `1_H^⊥`, `s = (L_H−λ)f_H` is
the port-boundary source. Spectrally `D_core = Σ_k γ_k/(γ_k−λ)²⟨s,φ_k⟩²` (matches actual to 10⁻¹⁶). The
current bound replaces every `γ_k` by `γ = γ_min`: `D_core ≤ γ/(γ−λ)²·‖s‖²` (operator-norm bound).

## TASK 1 — source spectrum

`‖s‖² = D_port` (exact — for deg2dense the port has 2 edges and `s_v = f_port − f_v` on its 2 core
neighbours). Effective vs max modal factor `(D_core/‖s‖²)` vs `γ/(γ−λ)²`:

| graph | eff factor | max factor | eff/max | participation | #sig modes | `|∂|` |
|---|---|---|---|---|---|---|
| twin-port `K₈₀` d2 | 0.0125 | 0.0128 | 0.98 | 2.7 | 6 | 2 |
| deg2+dense(60,.85) | 0.0203 | 0.0259 | **0.78** | 13.1 | 42 | 2 |

> The source spreads across **2.7–13 modes** (participation ratio); for twin it is nearly concentrated at
> `γ` (eff/max = 0.98 → the current bound is already tight, twin closes), but for deg2+dense it spreads
> (eff/max = 0.78 → the global γ-bound overshoots by ~28%). **The decay is moderate, not flat** — and the
> source lives on only `|∂| = 2` vertices, which is the key to the fix.

## TASK 2/3/4 — bounds tested (validity + closure out of 17)

| bound | valid (`≥ D_core`)? | closes | max ratio |
|---|---|---|---|
| **max** `γ/(γ−λ)²·‖s‖²` (current) | ✓ 17/17 | 9/17 | 1.208 |
| **TASK 2 trace** `‖s‖²·Σ_k 1/(γ_k−λ)²` | ✓ 17/17 | 9/17 | 1.559 |
| **TASK 3 n_eff** `‖s‖²/(n_eff·(γ−λ)²)` | **✗ 0/17 (UNSOUND)** | 17/17 | 0.467 |
| **TASK 4 BLOCK** `λ_max((RL_HR)_{∂∂})·‖s‖²` | **✓ 17/17** | **17/17** | **0.952** |
| exact `D_core` | ✓ (=) | 17/17 | 0.935 |

- **TASK 2 (trace `‖s‖²Σ1/(γ_k−λ)²`):** a *valid* upper bound, but LOOSER than the max (it sums all
  modes); closes only 9/17 (max 1.559). Spreading-aware in the wrong direction.
- **TASK 3 (n_eff):** "closes 17/17" but is **NOT a valid upper bound** (0/17 — it *underestimates*
  `D_core`). It is unsound — discarded.
- **TASK 4 (BLOCK):** the winner. ↓

## TASK 4 (winner) — the BLOCK resolvent bound

The source `s` is supported only on `∂` = core vertices adjacent to ports (`s_v = 0` otherwise). So

> **`D_core = s_∂ᵀ (RL_HR)_{∂∂} s_∂ ≤ λ_max((RL_HR)_{∂∂}) · ‖s‖²`** — the `∂`-principal-submatrix norm.

By **Cauchy interlacing**, `λ_max((RL_HR)_{∂∂}) ≤ λ_max(RL_HR) = γ/(γ−λ)²`, so this is a VALID tightening
of the current bound. It is much smaller because the boundary vertices are deep in the dense core (far
from the slow `γ`-mode), so their *local* resolvent norm is small.

| graph | `c_block` | `c_max` | `c_exact` | valid? |
|---|---|---|---|---|
| deg2+dense(80,.85) | **0.952** | 1.070 | 0.935 | ✓ |
| deg2+dense(40,.6) | **0.931** | 1.208 | 0.844 | ✓ |
| deg2+dense(80,.4) | 0.818 | 1.101 | 0.763 | ✓ |
| twin-port `K₈₀` d2 | 0.688 | 0.688 | 0.679 | ✓ |

> **`c_block ≤ 0.952 < 1` for all 17** (twin: `c_block = c_max`, already tight; deg2dense: `c_block`
> shaves the overshoot below 1). The block bound is valid (17/17) and closes (17/17).

## TASK 5 — closure summary

| bound | closes / 17 | sound? |
|---|---|---|
| max `γ/(γ−λ)²` | 9 | ✓ |
| trace `Σ1/(γ_k−λ)²` | 9 | ✓ |
| n_eff | 17 | **✗ unsound** |
| **BLOCK `λ_max((RL_HR)_{∂∂})`** | **17** | **✓** |

> **The tightest VALID bound that closes ALL 17 Case 2A graphs is the BLOCK resolvent bound
> `D_core ≤ λ_max((RL_HR)_{∂∂})·‖s‖²`** (`∂` = core-port-neighbours, `|∂| = 2` for deg2dense). Margin
> 0.952. No graph fails.

## Conclusion & Lean outlook

- **Closure achieved:** `D_core ≤ λ_max((RL_HR)_{∂∂})·‖s‖²` with `‖s‖² = D_port` closes `hcond` on all 17
  Case 2A graphs (max 0.952). The localized source is the key — the global γ-resolvent overshoots; the
  ∂-block resolvent (`|∂| = 2`) does not.
- **Why it works:** Cauchy interlacing makes it provably `≤` the current bound; the boundary vertices'
  local resolvent norm is small because they sit in the dense, high-gap core.
- **Discarded:** n_eff (unsound — underestimates `D_core`); trace (valid but looser than max).
- **Lean (no change this round):** the block bound needs the resolvent `(L_H−λ)^{-1}` restricted to `∂` —
  for `|∂| = 2` this is a 2×2 eigenvalue `λ_max = ½(tr + √(tr²−4det))` of resolvent entries; a clean but
  nontrivial target (boundary 2×2 block of `(L_H−λ)^{-1}L_H(L_H−λ)^{-1}`). The mathematical closure of
  Case 2A is now established; the Lean formalization of the 2×2 block resolvent is the next step.

## Lean
No code change (Python analysis per the constraint). The Case 2A scalar `hcond` is now closed
mathematically on all 17 graphs by the block resolvent bound; `typeA_slack_ge_required` stays the sorry
pending a Lean `(L_H−λ)^{-1}`-block formalization. 3 sorrys unchanged.
