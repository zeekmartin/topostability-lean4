# Conjecture B — nodal hard edges and the hub-flatness bound

Continue the per-edge attack on the aggregate triangle-Poincaré
`T = Σ_{ab∈E} t_ab(f_a−f_b)² ≤ λ₂·fᵀDf = λ₂·Σ_{ab∈E}(f_a²+f_b²)`, with per-edge surplus
`w_ab = t_ab(f_a−f_b)² − λ₂(f_a²+f_b²)`. The positive-`w` edges concentrate on the **hard set**

`H = { ab : t_ab ≥ λ₂  AND  f_a·f_b < 0 }`  (triangle-rich nodal-boundary edges).

We test whether the **hub-flatness lemma** (Paper14, `f_v² ≤ d_v/(d_v−λ₂)²` for a unit Fiedler
vector) is strong enough to bound the positive mass on `H` by the negative reservoir on the rest.
Code: [`conjecture_B_nodal_hard_edges.py`](../conjecture_B_nodal_hard_edges.py).
Corpus: 536 connected graphs (gnp + deg2-dense + deg-k + lollipop + Watts–Strogatz),
**432 with ≥1 hard edge, 15 864 hard edges total**.

**Headline — the true margin is real, but hub-flatness is the wrong tool.** The hard edges *are*
small in value (median `max(|f_a|,|f_b|) = 0.022`, median mass `f_a²+f_b² = 6·10⁻⁴`) and they
sit on **high-degree hubs** (median `d ≈ 31`), so hub-flatness holds with **~120× slack**
(actual mass is 0.8% of the hub-flatness bound). The *true* per-graph margin is comfortable:
`PosHard/NegEasy ≤ 0.43` on **every** graph (median 0.12) — the easy negative reservoir always
dominates the hard positive mass by **≥ 2.3×**. **But** the candidate hub-flatness bound
`HardBound = Σ_H (2t_ab−λ₂)·[d_a/(d_a−λ₂)² + d_b/(d_b−λ₂)²]` **fails in 95.4% of graphs**
(median overshoot 6.7×, worst 110×): the `(2t−λ₂)` prefactor (≈ degree) summed over hundreds of
hard edges swamps the small reservoir, even though each `f_v²` is genuinely tiny. **Hub-flatness
discards the very smallness it was meant to exploit.**

---

## TASK 1 — Are hard-edge endpoints small?

| quantity over 15 864 hard edges | min | median | max | mean |
|---|---|---|---|---|
| `max(|f_a|,|f_b|)` | 0.0022 | **0.0217** | 0.4047 | 0.0340 |
| mass `f_a²+f_b²` | 0.0000 | **0.0006** | 0.1643 | 0.0030 |
| `d_a` | 3 | **31** | 63 | 30.4 |
| `d_b` | 2 | **31** | 64 | 30.4 |
| `f_v²` / hub-flat(`d_v`) | 0.000 | **0.0082** | 0.248 | 0.0108 |

**Yes, in value — and they are high-degree hubs.** Hard-edge endpoints carry very little Fiedler
mass (median entry ~0.02, mass ~6·10⁻⁴), but they are *not* low-degree: median degree ≈ 31. The
smallness is the hub-flatness phenomenon — large `d_v` forces `f_v²` down. Crucially the bound is
far from tight: actual `f_v²` is only **0.8% (median)** of the hub-flatness ceiling.

## TASK 2 — Is the smallness explained by degree?

| quantity | min | median | max | mean |
|---|---|---|---|---|
| `t_ab / min(d_a,d_b)` | 0.143 | **0.625** | 0.938 | 0.612 |
| hub-flat bound on mass `Σ d/(d−λ₂)²` | 0.034 | **0.077** | 4.61 | 0.161 |
| actual mass / hub-flat bound | 0.000 | **0.0081** | 0.144 | 0.0111 |

**Degree explains the *direction* but vastly over-explains the *magnitude*.** Hard edges connect
near-saturated hubs (`t/min(deg) = 0.625`, i.e. most common neighbours are shared), so hub-flatness
*applies* — all 15 864 hard edges have both endpoints with `d_v > λ₂` (100%). But the bound is
**loose by ~120×**: it certifies `mass ≲ 0.077` while the truth is `~6·10⁻⁴`. Hub-flatness knows
the endpoints are small; it badly mis-estimates *how* small.

## TASK 3 — Total hard positive mass vs easy negative reservoir

| `PosHard / NegEasy` | max | median | mean |
|---|---|---|---|
| over 536 graphs | **0.4293** | 0.1223 | 0.1509 |

`PosHard = Σ_{ab∈H, w>0} w_ab`, `NegEasy = −Σ_{ab∉H, w<0} w_ab`. **The true margin is uniform and
safe: `PosHard < NegEasy` on 100% of graphs**, with worst case 0.43 (≥ 2.3× headroom). This is the
correct quantity to prove — and it always holds. The aggregate inequality is *never* close.

## TASK 4 — Candidate hub-flatness bound

`w_ab = (t−λ₂)(f_a²+f_b²) + 2t|f_a f_b| ≤ (2t−λ₂)(f_a²+f_b²) ≤ (2t−λ₂)·[d_a/(d_a−λ₂)² + d_b/(d_b−λ₂)²]`,
summed to `HardBound`.

| | value |
|---|---|
| `HardBound ≤ NegEasy` holds | **20/432 graphs (4.6%)** |
| `HardBound/NegEasy` (finite) max / median / mean | 110.6 / **6.68** / 17.6 |
| graphs with `HardBound = +∞` (some `d_v ≤ λ₂`) | **0** |
| worst case | n=73, m=2008, |H|=117, λ₂=1.99, HardBound=387.2, NegEasy=3.50 |

**The bound fails badly (95.4% of graphs).** It overshoots the reservoir by a median 6.7× and up
to 110×. Note it is never vacuous (`+∞`): every hard endpoint genuinely satisfies `d_v > λ₂`.
The failure is purely one of *looseness*, not applicability.

## TASK 5 — Why HardBound fails

The diagnosis isolates a single dominant cause:

- **Degree is high enough.** `t_ab/min(deg) = 0.625` (median) and 100% of hard endpoints have
  `d_v > λ₂`. Hub-flatness applies everywhere it is invoked — degree is **not** the problem.
- **The negative reservoir is ample.** True `PosHard/NegEasy ≤ 0.43` always — the reservoir is
  **not** too small. The margin we need to prove is genuinely there.
- **Hub-flatness is too loose — by ~120×.** Actual `mass/bound = 0.0081` (median). The lemma
  certifies each endpoint is small but over-estimates `f_v²` by two orders of magnitude.
- **The `(2t−λ₂)` prefactor amplifies the looseness.** Because hard edges live on hubs,
  `2t−λ₂ ≈ 2·(0.6·d) ≈ degree ≈ 36`. Multiplying a 120×-loose mass bound by a ~36 prefactor and
  summing over ~100+ hard edges per graph produces `HardBound` that is `~7×` the small `NegEasy`.

**Conclusion.** Per-edge hub-flatness cannot close the proof: it throws away exactly the smallness
(`f_v²` is 0.8% of its ceiling) that makes the aggregate true, then re-inflates by the degree-sized
prefactor `2t−λ₂`. Any working argument must either (i) keep the **anti-correlation** structure
`f_a f_b < 0` *together with* the gradient (rather than bounding `|f_a f_b| ≤ ½(f_a²+f_b²)` and
discarding sign), or (ii) bound the **collective** hard mass `PosHard` against `NegEasy` directly —
the true ratio is uniformly `≤ 0.43`, so the margin exists; it just is not localisable edge-by-edge
through hub-flatness. The next lever is the global anti-correlation/orthogonality `Σ_v d_v f_v = 0`
that hub-flatness ignores. See [`conjecture_B_anticorrelation_global.md`](conjecture_B_anticorrelation_global.md).
