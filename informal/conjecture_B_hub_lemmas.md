# Conjecture B — the two hub lemmas: one proven, one refuted, true mechanism found

Target: close B via `fᵀMf ≥ 0`, `M = λ₂Q − L_t`, by bounding the negative-cone
contribution. Code: [`conjecture_B_hub_lemmas.py`](../conjecture_B_hub_lemmas.py).

**Headline.**
- **LEMMA 2 (hub-flatness) is TRUE and Lean-provable:** `f_v² ≤ d_v/(d_v−λ₂)²`
  (0 violations / 78294 vertices), hub form `f_v² ≤ 4/d_v` for `d_v ≥ 2λ₂`
  (0/33507). Pure Cauchy–Schwarz + the eigen-equation.
- **LEMMA 1 (hub-localization of `M`'s negative eigenvectors) is FALSE as a universal
  statement:** 19% of negative directions are *not* hub-localized, some with `|μ|` up
  to 20.7 — yet `f` still avoids them. Hubs are only a partial proxy.
- **The TRUE mechanism is spectral SMOOTHNESS:** `M`'s negative cone consists of
  **high-L-energy (rough)** directions (`corr(μ, vᵀLv) = −0.84`), and the Fiedler `f`
  — the *smoothest* mode on `1⊥` — has small overlap with them (`corr(L-energy,
  |f·v|²) = −0.63`). This subsumes hub-localization and explains all negative
  directions, but it *is* the minimality of `λ₂` restated — not an independent
  elementary lemma.

---

## LEMMA 2 — hub-flatness (proof-ready)

From `Lf = λ₂f`: `(Af)_v = Σ_{u~v} f_u = (d_v − λ₂) f_v`. Cauchy–Schwarz:
`(Af)_v² = (Σ_{u~v} f_u)² ≤ d_v · Σ_{u~v} f_u² ≤ d_v · ‖f‖² = d_v`. Hence, for
`d_v ≠ λ₂`:

> **`f_v² ≤ d_v · Σ_{u~v} f_u² / (d_v − λ₂)²  ≤  d_v / (d_v − λ₂)²`.**

| test | result |
|---|---|
| `f_v² ≤ d_v/(d_v−λ₂)²` (78294 vertices) | **0 violations**; tightness `f_v²/bound` max 0.31, median 0.038 |
| hub form `f_v² ≤ 4/d_v` for `d_v ≥ 2λ₂` (33507 hubs) | **0 violations** |
| hub-mass `Σ_{d_v≥2λ₂} f_v²` vs bound `Σ d_v/(d_v−λ₂)²` (7516 graphs) | bound holds **7516/7516**; actual hub-mass median **0.094** (max 1.0) |

- **[2] Sharpening.** `Σ_{u~v} f_u²` has median **0.33** (≪ the crude `1`), so the
  bound is loose by ~3×; `d_v·Σ_{u~v}f_u²` has median 1.62, i.e. `Σ_{u~v}f_u² ≈
  1.6/d_v` — between `1/d_v` and a constant. A sharper neighbor-sum bound would tighten
  Lemma 2 but is not needed for the qualitative hub-flatness (mass is already small).
- **[4] Lean statement.** For unit Fiedler `f` (`L_G f = λ₂ f`) and any `v` with
  `d_v ≠ λ₂`: `f_v² · (d_v − λ₂)² ≤ d_v`. Proof = `lapMatrix` eigen-equation rewriting
  `(Af)_v=(d_v−λ₂)f_v` + finite-sum Cauchy–Schwarz (`Finset.inner_mul_le_norm_mul_norm`
  / `Finset.sum_mul_sq_le_sq_mul_sq`) + `Σf_u² ≤ 1`. **Self-contained; no `λ₂`-minimality
  needed** — this half is genuinely elementary and formalizable.

---

## LEMMA 1 — hub-localization of negative eigenvectors: REFUTED (universal form)

For `v_j` with `μ_j < 0`:

| step | result |
|---|---|
| [5] deg-weighted mass `Σ_v d_v v_j(v)²/d̄` | **min 0.55** across corpus (not always > 1) |
| [6] fraction of mass on `d_v ≥ median` | **min 0.000** (some have *zero* hub mass) |

Refining by strength of `μ`:

| `μ_j` band | n | hub-fraction (mean / min) | deg-mass/d̄ (mean) | mean `\|f·v\|²` |
|---|---|---|---|---|
| strong `μ<−3` | 5417 | 0.83 / 0.00 | 1.12 | 0.0035 |
| mid `−3..−1` | 833 | 0.56 / 0.00 | 0.93 | 0.0163 |
| weak `−1..0` | 411 | 0.49 / 0.00 | 0.90 | 0.0228 |

Negative directions are hub-localized *on average*, more so when strongly negative
(`corr(μ, hubfrac) = −0.49`), but **1284/6661 (19%) have hub-fraction < 0.5, with `|μ|`
up to 20.7** — strongly negative yet *not* on hubs. `f` avoids these too
(`|f·v|²≈0.012`). So "negative ⇒ hub-localized" is **false**, and the avoidance of the
non-localized negatives needs a different explanation.

---

## The true mechanism — spectral smoothness (subsumes hubs)

The negative cone of `M = λ₂Q − L_t` is the **high-L-energy** (rough) subspace:

| quantity | value |
|---|---|
| mean normalized L-energy `vᵀLv/λ_n` of NEG-`M` directions | **0.82** |
| same for POS-`M` directions | 0.43 |
| `corr(μ_j, vᵀLv)` | **−0.84** |
| `corr(vᵀLv, \|f·v\|²)` | **−0.63** |
| NEG-`M` directions' L-energy: median | 0.86 |

So `M`'s negative directions are **rough** (high `L`-energy), and the Fiedler `f` —
the **smoothest** non-trivial mode (minimizer of `vᵀLv` on `1⊥`) — has systematically
small overlap with them. This explains the avoidance for *all* negative directions
(including the 19% non-hub ones): hubs are a proxy for roughness, but roughness
(`L`-energy) is the real driver. The hub picture works where rough = hub-localized and
fails otherwise; the smoothness picture is exact.

**But this is `λ₂`-minimality.** "`f` avoids high-L-energy directions because it is the
lowest-L-energy mode" is precisely Courant–Fischer minimality. Concretely
`⟨f,v_j⟩ = ⟨u₂,v_j⟩` and `negative_part = u₂ᵀ M_{<0} u₂` — bounding it below the
positive part is `fᵀMf ≥ 0`, i.e. B itself. No elementary shortcut emerges; the
mechanism is real but circular as a *proof*.

---

## Closure test (step 8)

| quantity | result |
|---|---|
| actual `neg_part ≤ pos_part` | **1500/1500** (= B), with margin **neg/pos ≤ 0.09** (median 0.018) |
| lemma-product bound `≤ pos_part` | only **21/1500**; bound/pos median **3.4**, max 17 |

The genuine avoidance is *very* strong (negative part ≤ 9% of positive). But the
hub-lemma product bound on `⟨f,v_j⟩²` (Cauchy–Schwarz split into hub/non-hub) is **too
lossy** (median 3.4× over) *and* rests on the refuted Lemma 1 — so the two-lemma
program does **not** close B quantitatively. The slack is there; the hub bookkeeping
wastes it.

---

## Literature (step 7) — Schrödinger / Agmon framing

`M = L_t − λ₂Q` is a discrete Schrödinger operator "kinetic `L_t` − potential `λ₂Q`" on
the triangle-weighted graph; negative-`M` eigenvectors are its low-lying states. The
relevant body of work is **Agmon estimates on graphs**
([An Agmon estimate for Schrödinger operators on Graphs, arXiv:2206.09521](https://arxiv.org/abs/2206.09521);
[Agmon estimates …, arXiv:2104.04737](https://arxiv.org/pdf/2104.04737)) and the
**landscape function** for M-matrices
([Landscape approximation of the ground state eigenvalue, ScienceDirect](https://www.sciencedirect.com/science/article/abs/pii/S0022123624000272)):
eigenfunctions decay exponentially in the classically-forbidden region (potential >
energy). These give *localization* templates, but they bound a *fixed* operator's
eigenfunctions, whereas our `M` is `λ₂`-coupled and the quantity we need is the overlap
of an *external* vector (`f`) with the low-lying cone — not covered off-the-shelf.

---

## Synthesis

- **LEMMA 2 (hub-flatness) is a real, elementary, Lean-ready result** —
  `f_v²(d_v−λ₂)² ≤ d_v` from the eigen-equation + Cauchy–Schwarz, 0 violations. Worth
  formalizing regardless, as the first non-trivial spectral fact in this project that
  needs *only* the eigen-equation.
- **LEMMA 1 (hub-localization) is refuted** as a universal statement; the negative cone
  is characterized by **roughness (high L-energy), not degree** (`corr −0.84`).
- The avoidance that makes B true is a **smoothness/minimality** phenomenon, confirming
  the standing conclusion: the proof needs `λ₂`-minimality used to bound `f`'s overlap
  with the high-L-energy cone — which is `fᵀMf ≥ 0` restated. The two-lemma product is
  too lossy to serve as the certificate.

### Caveats
`λ₂`, `f`, `M`-spectra numerical. LEMMA 2 over all 9020 corpus graphs (78294 vertices);
LEMMA 1 / smoothness / closure over a 1500-graph sample (6661 negative directions).
The reduction `B ⟸ B2′` is rigorous; LEMMA 2 is proof-ready; B itself remains unproven.
