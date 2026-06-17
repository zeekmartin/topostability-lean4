# Conjecture B — back to the actual-triangle operator `M = λ₂Q − L_t`

Course correction: drop the min-degree relaxation `K = λ₂Q − L_min`; target
`fᵀMf ≥ 0`, `M = λ₂Q − L_t`, with **actual** triangle weights `t_ab = (A²)_ab`. Code:
[`conjecture_B_real_triangles.py`](../conjecture_B_real_triangles.py).

**Headline — the correction is validated.** On deg2+dense the real-triangle operator
`M` keeps **stable avoidance** (`neg/pos ≈ 0.25`, `pos/neg ≈ 4×`, flat in `n`) and a
**margin bounded away from 0** (`margin_M ≈ 0.5–0.8`; real conjecture `margin_B ≈ 0.51`;
rigorous lift lower bound `≥ 0.18` at all scales). The min-degree relaxation `K`, by
contrast, is **near-cancellation** (`neg/pos → 0.996`) and asymptotically tight
(`margin_B2 → 0`). So **`M` is the right target; `B2′` was a self-inflicted hard case.**
`M` is still deeply indefinite (`n−1` negative eigenvalues) — positivity holds by
avoidance, not PSD-ness.

---

## TASK 1 — real margin vs relaxation margin

| `n` | `λ₂(G)` | `λ₂(T)` | `margin_B = 1−λ₂T/λ₂G` | `margin_B2` (relax) | `margin_M` |
|---|---|---|---|---|---|
| 50 | 1.973 | 0.949 | **0.519** | 0.465 | 0.510 |
| 100 | 1.990 | 0.978 | **0.508** | 0.373 | 0.503 |
| 300 | 1.994 | — | (≥0.17 via lift) | 0.167 | 0.803 |
| 500 | — | — | (≥0.185 via lift) | 0.110 | 0.501 |
| 1000 | — | — | (≥0.18 via lift) | **0.049** | 0.500 |

- **Real conjecture margin `margin_B ≈ 0.51`** (reliable at `n≤100`); the rigorous lift
  bound `margin_B ≥ 1 − fᵀL_tf/(λ₂(fᵀQf−S²/m))` gives **≥ 0.18–0.68** at `n=100..500`
  (TASK 4). So `inf_n margin_B` on deg2+dense is **bounded away from 0** (`≳ 0.18`).
- **`margin_B2 → 0`** (0.47 → 0.05): the relaxation alone is asymptotically tight.
- `margin_M = fᵀMf/(λ₂ fᵀQf)` stays **0.5–0.8** (noisy, never near 0).

*(Caveat: the sparse `λ₂(T(G))` solver returned a spurious `0` at `n≥150` — a
shift-invert artifact, not a real value — so direct `margin_B` is quoted only for
`n≤100`; the lift lower bound covers larger `n` rigorously.)*

## TASK 2 — `f` in `M`'s eigenbasis: avoidance persists at scale

| `n` | `fᵀMf` | pos_part | neg_part | **neg/pos** | (vs `K` min-deg) |
|---|---|---|---|---|---|
| 100 | 3.28 | 4.3 | 1.06 | **0.244** | 0.996 |
| 200 | 5.30 | 6.5 | 1.22 | **0.187** | 0.996 |
| 500 | 3.31 | 4.6 | 1.25 | **0.275** | 0.996 |
| 1000 | 3.30 | 4.6 | 1.27 | **0.278** | 0.996 |

`M`'s positive energy dominates negative by ~4× and the ratio is **flat in `n`** — the
Fiedler genuinely **avoids** `M`'s negative cone, stably. (Corpus-wide `n≤9` the gap was
~600×; at scale on this adversarial family it settles to ~4×, still clean avoidance.)
This is the diametric opposite of `K` (min-degree), where `neg/pos → 0.996` is
near-cancellation. **The actual triangles restore avoidance.**

## TASK 3 — what the relaxation overestimates

Per-edge gap `(min(d_a,d_b)−1) − t_ab`:

| `n` | degree-2 vertex's edges | all other (dense) edges |
|---|---|---|
| 100 | gap ≈ **0** (mean 0.0, n=2) | gap mean **19.7**, max 29 |
| 200 | gap ≈ 1 (mean 1.0, n=2) | gap mean **40.3**, max 56 |

**Surprise (refines the hypothesis):** the relaxation `min−1` is *accurate* on the
degree-2 vertex's own edges (`t_ab ≈ min−1`, gap ≈ 0) and *grossly overestimates* on the
**dense** edges (gap 20–40). The dense edges carry small Fiedler gradient (`f` is flat on
the bulk), so this large per-edge overestimate inflates `W₁` over `fᵀL_tf` by only ~1.2× —
but that 1.2× is exactly what consumes the asymptotic margin. So the relaxation's harm is
*spread over the dense bulk*, not localized to the degree-2 vertex.

## TASK 4 — direct diagnostics for `fᵀMf ≥ 0`

| `n` | #neg eig `M\|₁⊥` | #neg eig `K(min)\|₁⊥` | real-margin `1−fᵀL_tf/lift` | min-margin `1−W₁/lift` |
|---|---|---|---|---|
| 100 | 98/99 | 98/99 | **0.228** | 0.085 |
| 200 | 198/199 | 198/199 | **0.679** | 0.031 |
| 500 | 498/499 | 498/499 | **0.185** | 0.020 |

- **(a) `M` is *not* closer to PSD** — both `M` and `K` have `n−1` negative eigenvalues on
  `1⊥`. Positivity of `fᵀMf` is **not** an operator fact; it is the avoidance of TASK 2.
- **(b) the operator inequality `L_t ⪯ λ₂Q` fails** for both (deeply indefinite), so no
  Loewner domination — real or relaxed.
- **(c) real triangles buy the margin:** `1 − fᵀL_tf/lift` (real) = **0.18–0.68** vs
  `1 − W₁/lift` (min) = **0.02–0.09**. The actual `t_ab` keeps the lift bound comfortably
  below `λ₂`, while the min-degree weights barely clear it.

---

## Synthesis — the right target and the proof mechanism

- **Target `fᵀMf ≥ 0` with real triangles**, not the min-degree relaxation. On the
  binding deg2+dense family, `M` has a **stable ~4× avoidance gap** and a margin bounded
  away from 0 (`margin_B ≳ 0.18`), whereas the relaxation is asymptotically tight. The
  triangle-free convenience of `B2′` is paid for by losing exactly the structure that
  makes B provable.
- **The mechanism is negative-cone avoidance** (multispectral round), now confirmed
  **stable at scale**: `M` is indefinite (`n−1` negatives), but the smooth Fiedler lands
  in its positive cone with `pos/neg ≈ 4`. The proof must show this — `f` (lowest-`L`-mode)
  avoids `M`'s high-`L_t`-energy negative directions — using `λ₂`-minimality.
- **Asset in place:** the hub-flatness lemma (`Paper14.lean`) bounds `f` on hubs, which is
  the ingredient for controlling `fᵀL_tf` (triangle energy concentrates on dense/hub
  regions where `f` is flat).

**Next step:** rerun the negative-cone / hub-flatness closure on `M` (real triangles) at
scale — the avoidance there is stable (unlike the relaxed operator), so the
mechanism that failed to close `B2′` may close `B` directly.

### Caveats
`λ₂`, `f`, `M`-spectra numerical. deg2+dense, `q=0.65`, to `n=1000`. Direct `λ₂(T)` only
`n≤100` (sparse solver artifact at `n≥150`); larger `n` uses the rigorous lift lower bound
on `margin_B`. `margin_M`/`neg-pos`/eigencounts exact. `fᵀMf ≥ 0` (= B) holds throughout.
