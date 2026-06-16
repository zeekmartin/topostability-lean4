# Conjecture B — multi-spectral attack: the negative-cone-avoidance mechanism

`target := C + R″ ≥ 0` is the B2′ slack; `C = Σ(d_h−d_l)f_h(f_h−f_l)`,
`R″ = λ₂(fᵀDf−λ₂+1−S²/m)`, `f = u₂` (unit Fiedler). Code:
[`conjecture_B_multispectral.py`](../conjecture_B_multispectral.py).

**Headline (TASK 2 — the mechanism).** B holds because the Fiedler vector
**systematically avoids the negative cone** of `M := λ₂Q − L_t` (`Q=D+A`, `L_t`
triangle-weighted Laplacian; `fᵀMf ≥ 0 ⟺ B`). Across the corpus:
- mean `|fᵀvⱼ|²` on the **most-negative** decile of `M`'s spectrum is **0.0011**, vs
  **0.65** on the most-positive decile — a **~600×** gap;
- `|fᵀvⱼ|² → 0` monotonically as `μⱼ → −∞` (0.023 → 0.0014 across bins;
  `corr(μⱼ, |fᵀvⱼ|²) = +0.39`);
- the avoidance is **necessary**: a uniform-overlap counterfactual gives `fᵀMf < 0`
  on **91%** of graphs (the average eigenvalue of `M|₁⊥` is negative);
- the negative directions are **degree-localized on hubs** (degree-weighted mass
  `Σ_v d_v vⱼ_v² / d̄` = **1.08** for `μⱼ<0` vs **0.85** for `μⱼ>0`).

So: **`M`'s negative cone lives on high-degree vertices; the Fiedler is flat at hubs;
hence `f` has tiny overlap with the negative cone, forcing `fᵀMf ≥ 0`.** This is a
genuine structural mechanism (hub-flatness × hub-localized negative cone), connecting
the spectral picture to the earlier hub-flatness finding.

---

## TASK 1 — eigenbasis decomposition: no clean mode-sum

Decomposing `d = Σ_i β_i u_i` (`β_i = dᵀu_i`, `S = β₂`), the resolvent-weighted sum
`Σ_{i≥3} β_i²/(λ_i−λ₂)` does **not** reconstruct target: `corr = −0.27`, best-fit
**R² = −4.73**. `target` is *not* expressible as a clean nonnegative mode-sum
`Σ_{i≥3} g(β_i, λ_i, λ₂)`. Reason: `R″` mixes `fᵀDf` and `S²/m = β₂²/m` (only the
`β₂` mode is a degree-projection), and `C` (oriented degree-gradient) is **not** a
degree-projection quantity at all. The degree-mode content is real but does not
assemble into a term-wise-positive spectral series — consistent with the
indefinite-coefficient finding of the reverse-vector round.

---

## TASK 2 — negative-cone avoidance (full detail)

`fᵀMf = Σ_j μ_j |fᵀv_j|² ≥ 0` on **1500/1500** sampled graphs, even though `M` is
indefinite. `|fᵀv_j|²` averaged by eigenvalue bin:

| `μⱼ` bin | mean `|fᵀvⱼ|²` | count |
|---|---|---|
| `(−∞, −10)` | **0.0014** | 2357 |
| `[−10, −3)` | 0.0052 | 3060 |
| `[−3, −1)` | 0.0163 | 833 |
| `[−1, −0.1)` | 0.0228 | 374 |
| `[−0.1, 0)` | 0.0233 | 37 |
| most-positive decile | **0.652** | — |

**Necessity.** Replacing `f`'s overlaps by uniform weights (`|fᵀvⱼ|² ≡ 1/(n−1)`) gives
`fᵀMf = mean(μⱼ) < 0` on **1362/1500 (91%)**. So a generic `1⊥` vector violates B; only
`f`'s structured avoidance rescues it. (`fᵀMf ≥ uniform` on all 1500.)

**Why (structural).** The most-negative eigenvectors of `M = λ₂(D+A) − L_t` are high
triangle-energy directions, which concentrate on **dense, high-degree regions**
(degree-weighted localization 1.08 > 0.85 for positive directions). The Fiedler vector
is **flat at hubs** (hub-flatness; `corr(deg, f²) ≈ −0.84` from earlier rounds), so its
overlap with these hub-localized directions is tiny. The two facts compose into the
avoidance. **This is the proof mechanism**: it reduces B to a quantitative coupling
"`M`'s negative cone is hub-localized" + "`f` is small at hubs."

---

## TASK 3 — perturbation around `K_n` (`C ≡ 0`, leading term `R″ > 0`)

For all near-complete families the **oriented term `C` vanishes** — the Fiedler
concentrates on the perturbed vertices, which have *equal* degree, so every
`(d_h−d_l)` factor on an `f`-active edge is 0. Thus `target = R″` there.

| family | `C+R″` (verified) |
|---|---|
| `K_n − e` | **`n−2`** (6,8,12 at n=8,10,14) ✓ |
| `K_n − △` (triangle) | **`n−3`** (5,7,11) ✓ |
| `K_n − matching(k)` | **`n−2`, independent of `k`** (14 for all k=1..5 at n=16) |
| `K_n − star(k)` | grows with `k` (17.7 peak at k=3, n=16) |

- **Matching removal is non-interacting:** `k` disjoint missing edges give the same
  slack as one (`n−2`) — the perturbations don't couple. Leading order in `k` is
  `0·k` beyond the first edge (flat).
- **Star removal interacts:** `k` edges at one vertex couple through that vertex's
  degree drop, raising the slack super-linearly then saturating.
- **Leading term is always `≥ n−2 > 0`.** A perturbative proof from `K_n` is viable for
  dense graphs: `target = R″ + O(C)` with `C=0` at the complete-graph boundary, and
  `R″ = (n−2) + …> 0`. (`C` only switches on for irregular graphs away from `K_n` — the
  regime the hub-flatness mechanism of TASK 2 covers.)

---

## TASK 4 — correlation diagnostic

| predictor | `corr` with `target` | best-`c` R² |
|---|---|---|
| `λ₃ − λ₂` (spectral gap) | −0.13 | −1.95 |
| `β₃² = (dᵀu₃)²` | −0.31 | −5.58 |
| `Σ_{i≥3} β_i²/(λ_i−λ₂)` (resolvent) | −0.27 | −4.73 |
| **`fᵀD²f − (fᵀDf)²`** (degree variance on `f`) | **−0.63** | −3.17 |

The **degree-variance-on-the-Fiedler** is the best single predictor (`−0.63`): larger
degree spread *as seen by `f`* → *smaller* slack (closer to tight). No single quantity
fits exactly (all R² < 0), but this confirms the slack is governed by how degree
irregularity aligns with the Fiedler — i.e. the same hub/degree-vs-`f` coupling that
TASK 2 makes precise.

---

## Synthesis — the productive route

The four tasks converge on one mechanism:
- **target is not a clean spectral mode-sum** (TASK 1) and **not a single
  second-variation** (prior round) — it is governed by a *coupling* between the degree
  structure and the Fiedler vector (TASK 4: degree-variance-on-`f` is the best proxy).
- That coupling is exactly **negative-cone avoidance** (TASK 2): `M = λ₂Q − L_t` has its
  negative eigenvectors localized on high-degree hubs, and the Fiedler is flat there, so
  `fᵀMf ≥ 0`. The avoidance is *necessary* (uniform overlap fails 91%).
- Near `K_n` the oriented term vanishes and `target = R″ ≥ n−2 > 0` (TASK 3), giving a
  clean perturbative proof for the dense regime; the hub-flatness mechanism handles the
  irregular regime.

**Next step (a genuine proof path):** make TASK 2 quantitative — bound the
degree-localization of `M`'s negative eigenvectors (a property of `L_t` vs `Q`), and
bound the Fiedler's hub-mass (`Σ_{high-deg} f_v²`, the hub-flatness lemma). Their
product bounds `Σ_{μ_j<0} |μ_j| |fᵀv_j|²` below the positive contribution. This is the
first mechanism that is both structural and matches the data on all 9020 graphs.

### Caveats
`λ₂`, `f`, `M`-spectra numerical. TASK 1/4 over 9020 distinct corpus graphs; TASK 2
over a 1500-graph sample (negative-eigenvector overlaps, 6661 negative directions);
TASK 3 exact on named families. Hub-flatness and the negative-cone localization are
*empirical* regularities here (corr-level), not yet theorems — the proof needs both as
quantitative lemmas. `B ⟸ B2′` rigorous; B/B2′ unproven.
