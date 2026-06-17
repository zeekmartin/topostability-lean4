# Harmonic-mass quantity `H(f) = Σ_v f_v²/d_v` — empirical test

`f` = unit Fiedler vector, `d_v` = degree. Code:
[`harmonic_mass_test.py`](../harmonic_mass_test.py). Corpus: 9020 distinct graphs
(`n≤9`, `T(G)` connected).

**Headline.** `H(f) ≤ 1` holds with **0 violations**, but it is *not* a tight/binding
bound: the real ceiling is `H(f) ≤ 1/δ` (a trivial Rayleigh bound, `δ=`min degree),
so **max H = 0.5** on this corpus (`δ=2`), never near 1, and `H=1` is never achieved.
`H ≤ 1` is **not Fiedler-specific** — it holds for every eigenvector (and indeed every
unit vector). The genuinely interesting fact is the **very strong inverse correlation
`corr(H, C+R″) = −0.935`** with the B2′ slack.

---

## 1. Is `H(f) ≤ 1`? — yes, 0 violations, but loosely

| | value |
|---|---|
| violations `H > 1` | **0 / 9020** |
| max `H(f)` | **0.500000** |

`H ≤ 1` holds, but trivially: for any unit `x`, `H(x) = Σ x_v²/d_v ≤ (1/δ)·Σ x_v² =
1/δ`. The corpus has `δ ≥ 2` (forced by `T(G)` connected), so `H ≤ 1/2` — the `≤ 1`
bound is never within 2× of binding.

## 2. Distribution

| min | median | mean | max |
|---|---|---|---|
| 0.1250 | 0.2900 | 0.3002 | 0.5000 |

## 3. Graphs closest to the (irrelevant) value 1 — i.e. largest `H`

All maximizers have `H = 0.5` exactly, are **small with a degree-2 vertex** and
`λ₂ = 2`: `n=4,m=5` (`K₄−e`), `n=5,m=7`, `n=6,m=9`, `n=7,m=11`, … (`d ∈ [2, …]`). These
are graphs where the Fiedler vector **localizes on two minimum-degree (degree-2)
vertices** with `±` equal mass: then `H = ½·(1/2) + ½·(1/2) = 1/2 = 1/δ`. So "closest
to 1" really means "attains `1/δ`", a localization phenomenon, not closeness to 1.

## 4. Is `H = 1` achieved? — no

**0 graphs** with `H = 1`. It would require `δ = 1` *and* all Fiedler mass on a single
degree-1 vertex — impossible since `f ⊥ 1` forbids a one-vertex support. Max attained is
`1/δ = 0.5`.

## 5. Correlation with the B slack — strong (`−0.935`)

> **`corr(H(f), C+R″) = −0.935`.**

This is the strongest single correlate of the B2′ slack found in this project (cf.
degree-variance-on-Fiedler `−0.63`, spectral gap `−0.13`). Larger `H` (Fiedler mass on
*low*-degree vertices) ⟺ *smaller* slack. Direction matches the mechanism: the slack is
governed by how Fiedler mass sits relative to degree, and `H` is a clean scalar proxy
for "mass on low-degree vertices". `H` itself is `≤ 1/2`, so it is a **predictor**, not a
certificate (it cannot directly bound `C+R″ ≥ 0`).

## 6. Cauchy–Schwarz identity `H(f)·fᵀDf ≥ 1`

Holds **9020/9020**, min **exactly 1.00000**. This is Cauchy–Schwarz:
`1 = (Σ f_v²)² = (Σ (f_v/√d_v)(f_v√d_v))² ≤ (Σ f_v²/d_v)(Σ d_v f_v²) = H(f)·fᵀDf`.
**Equality (`H·fᵀDf = 1`) holds iff `d_v` is constant on the support of `f`** (where
`f_v ≠ 0`), *not* iff `G` is regular: 112 graphs attain equality and they are **not all
regular** (e.g. `K_n−e`, where `f` is supported on the two equal-degree non-adjacent
vertices, gives CS-equality despite global irregularity). This is the exact equality
characterization; the earlier guess "⟺ regular" is too strong.

---

## Higher eigenvectors — `H ≤ 1` is not Fiedler-specific

`H(u_k)` for `u_2`(Fiedler)…`u_7` over an 800-graph subsample:

| eigenvector | max `H` | median | violations `H>1` |
|---|---|---|---|
| `u_2` (Fiedler) | 0.500 | 0.305 | 0/800 |
| `u_3` | 0.500 | 0.255 | 0/800 |
| `u_4` | 0.500 | 0.243 | 0/800 |
| `u_5` | 0.500 | 0.222 | 0/798 |
| `u_6` | 0.341 | 0.208 | 0/792 |
| `u_7` | 0.275 | 0.190 | 0/765 |

`H ≤ 1` (indeed `≤ 1/δ = 0.5`) holds for **all** eigenvectors, with no violations. So
`H ≤ 1` is a property of *any unit vector* (`H ≤ 1/δ`), carrying **no Fiedler-specific
content**.

---

## Synthesis

- `H(f) ≤ 1` is true but vacuous — it is the trivial Rayleigh bound `H ≤ 1/δ ≤ 1/2`,
  not special to the Fiedler, never close to 1, never equal to 1.
- The Cauchy–Schwarz identity `H·fᵀDf ≥ 1` is exact, with equality ⟺ degree constant on
  `supp(f)`.
- The one substantive finding is **`corr(H, C+R″) = −0.935`**: `H` is an excellent
  *scalar predictor* of the B2′ slack (mass-on-low-degree ⟺ small slack), the best yet,
  though as a sub-`½` quantity it is not itself a nonnegativity certificate for `C+R″`.

### Caveats
`λ₂`, `f` numerical; all over the 9020 distinct corpus graphs (`n≤9`), higher
eigenvectors over an 800-graph subsample. `H ≤ 1` and `H·fᵀDf ≥ 1` are exact-by-
Cauchy–Schwarz facts; the `−0.935` correlation is empirical and not an identity.
