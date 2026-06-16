# Conjecture B — vertex-local decomposition of Δ: no local certificate exists

`B ⟺ Δ = λ₂·φᵀ(D+A)φ − Σ_{c∈V} 𝓔_{G[N(c)]}(φ) ≥ 0` (apex form, `φ=f` Fiedler).
Tested whether `Δ` can be certified **vertex-by-vertex**. Code:
[`conjecture_B_local_decomposition.py`](../conjecture_B_local_decomposition.py).
Corpus: 9,020 distinct graphs + deg2+dense lock-breakers + `K_n` families.

**Verdict: no vertex-local decomposition certifies B.** Every local scheme fails —
the natural split `Δ_c ≥ 0` (0.1%), the local Poincaré (b) (6% of vertices), the
degree-weighted split (85.9%, best but still fails), and the corrected Poincaré (c)
(needs a vertex-dependent correction up to `2.26×` the local mass). `Δ` is
**irreducibly global**: its sign *anti-correlates* with where the Fiedler lives.

(Note: the brief's split had a factor-2 typo — `φᵀ(D+A)φ = Σ_v d_vφ_v² +
2Σ_{uv∈E}φ_uφ_v`, so the correct local term is `φ_c·((D+A)φ)_c`, no `/2`. With that
fix `Σ_c Δ_c = Δ` exactly, verified to `1e-14`.)

---

## 1–2. The natural split `Δ_c = λ₂·φ_c·((D+A)φ)_c − 𝓔_{G[N(c)]}(φ)`

`Σ_c Δ_c = Δ` confirmed (max err `1.24e-14`). But **vertex positivity fails
badly:** only **10 / 9020 graphs (0.1%)** have all `Δ_c ≥ 0`.

**Why (from `K_n − e`):** for a *bulk* vertex `c` (`f_c = 0`),
`Δ_c = −𝓔_{G[N(c)]}(φ) ≤ 0` — it carries the local energy but none of the mass.
For the *perturbed* endpoints `0,1` (`f_c = ±1/√2`),
`Δ_c = λ₂·f_c·((D+A)f)_c = (n−2)²/2 > 0`. So:

| `K_n − e`, vertex type | `f_c²` | `Δ_c` | local Poincaré ratio |
|---|---|---|---|
| removed-edge endpoints (deg `n−2`, ×2) | 1/2 | **+(n−2)²/2** (e.g. +18, n=8) | 0 |
| bulk (deg `n−1`, ×(n−2)) | 0 | **−(n−3)** (e.g. −5, n=8) | 0.83–0.90 |

`Δ = 2·(n−2)²/2 − (n−2)(n−3) = n−2 > 0` — a **global balance**: large positive
surplus at the perturbation site (where `f` lives) outweighs the spread deficit in
the bulk. The "−1 drop" is **not localized** to specific vertices in any sign-
definite way; the bulk vertices that merely *see* `f` (but don't carry it) have
`Δ_c < 0`.

## 3. (b) The local Poincaré — the candidate proof — FAILS

`𝓔_{G[N(c)]}(φ) ≤ λ₂(G)·Σ_{v∈N(c)}φ_v²` (which, summed, would give B since
`φᵀAφ ≥ 0` for non-complete `G`):

- per-vertex violations: **4967 / 78708 = 6.31%**;
- non-complete graphs with ≥1 violation: **3324 / 9014 = 36.9%**;
- worst local ratio `𝓔/(λ₂·mass) = 3.26`;
- on the **deg2+dense lock-breaker family**: **37.3%** of vertices violate, **all
  115** graphs have a violation (worst ratio 2.50).

So (b) is **false** — local subgraphs `G[N(c)]` can carry Fiedler energy far above
`λ₂(G)·mass`. It holds for `K_n` (ratio 0.84–0.91) and `K_n−e` (the perturbed
vertices have ratio 0, bulk 0.83–0.90), but not in general. **Not a proof route.**

## 4. (a) Degree-weighted split & (c) corrected Poincaré

- **(a)** `Δ_c^{deg} = λ₂·(d_c/2m)·φᵀ(D+A)φ − 𝓔_{G[N(c)]}(φ)`: all `Δ_c^{deg} ≥ 0`
  on **7745 / 9020 = 85.9%** of graphs — much better than the natural split (0.1%),
  but **still fails on 14%**. So even proportional-to-degree attribution is not a
  certificate.
- **(c)** the correction needed to rescue (b),
  `𝓔_{G[N(c)]}(φ) ≤ λ₂(Σφ² + k_c·mass)`: where (b) fails, `k_c` has median `0.173`
  and **max `2.26`** (as a multiple of local mass) — **vertex-dependent, no clean
  global form**. The honest correction is `λ_max(L_{G[N(c)]})` (the *local* top
  eigenvalue), which is `≫ λ₂(G)` — not usable.

## 5. Is the drop localized? — No (anti-localized)

For `K_n−e` (and `K_n−△`), the discriminant is **concentrated positive at the
perturbation site** (the high-`f` vertices) and **negative across the bulk**. The
net `Δ = n−2` (resp. `n−3`) is a global cancellation, not a local loss. So the
mechanism is the *opposite* of local: positivity requires the few `f`-carrying
vertices to overcome the deficit spread over all vertices whose neighborhoods
contain them.

---

## Synthesis

| local scheme | certifies B (all-vertex ≥0 / no-violation)? |
|---|---|
| natural split `Δ_c = λ₂φ_c(Qφ)_c − 𝓔_{N(c)}` | ❌ 0.1% |
| **local Poincaré (b)** `𝓔_{N(c)} ≤ λ₂·mass` | ❌ 6.3% of vertices, 36.9% of graphs |
| degree-weighted split (a) | ◐ 85.9% (still fails 14%) |
| corrected Poincaré (c) | ❌ correction vertex-dependent, up to 2.26×mass |

**No vertex-local decomposition certifies B.** `Δ ≥ 0` is a genuinely *global*
spectral fact: the local discriminant is negative exactly at the vertices whose
neighborhoods "see" the Fiedler mass without carrying it, and positivity is a
global cancellation dominated by the `f`-support. This rules out the
"local-energy-balance" proof strategy (and matches the earlier dead ends: the
obstruction is always that the controlling quantity lives on a *different* set of
vertices/edges than where `f` concentrates).

The genuine open core is unchanged and remains global:
**`Σ_{(a,b)∈E} t_{ab}(f_a−f_b)² ≤ λ₂(G)·fᵀ(D+A)f`** for the Fiedler `f`. The apex
identity and `Σ_c Δ_c = Δ` are exact and useful for *bookkeeping*, but the
positivity does not decompose.

### Caveats
- `λ₂`, `f` numerical; `Σ_c Δ_c = Δ` verified to `1e-14`. (b)/(a)/(c) rates over the
  9,020 distinct corpus graphs (+ 200 deg2+dense, `n` up to 29). No new Lean this
  round — all four local candidates were refuted numerically; the apex identity
  `hᵀL_T h = Σ_c 𝓔_{G[N(c)]}(φ)` (and its per-edge core) was Lean-verified earlier.
