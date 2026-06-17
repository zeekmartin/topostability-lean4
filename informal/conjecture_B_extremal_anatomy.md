# Conjecture B — extremal anatomy on deg2+dense (the binding family)

Three experiments on deg2+dense, where B2′ is asymptotically tight. `C+R″ = fᵀKf`,
`K = Q_C + λ₂(A + I − ddᵀ/m)`, `Q_C` the oriented-`C` quadratic form. Code:
[`conjecture_B_extremal_anatomy.py`](../conjecture_B_extremal_anatomy.py).

**Headline.** On deg2+dense the nonnegativity `C+R″ ≥ 0` is achieved by **near-perfect
cancellation**, not avoidance: in `K`'s eigenbasis `f` has positive and negative
energy ~26 each, differing by the tiny `C+R″ ≈ 0.1` (`neg/pos → 0.996`). This is the
*opposite* of the actual-triangle operator `M=λ₂Q−L_t` (600× avoidance gap). **The
culprit is the min-degree relaxation**: the true-triangle slack keeps a comfortable
margin (0.18–0.68) while the min-degree-relaxed `C+R″` margin decays as `~n^{−0.66}`. The
aggregation loss in the per-vertex bound is **per-vertex looseness (6×), not sign
cancellation (1.1×)** — the negativity is concentrated at the single degree-2 vertex.

---

## TASK A — cancellation vs avoidance (it's cancellation)

`f` decomposed in `K`'s eigenbasis (`fᵀKf = C+R″ = Σ μᵢ αᵢ²`):

| `n` | `C+R″` | pos_part | neg_part | neg/pos |
|---|---|---|---|---|
| 50 | 0.523 | 3.63 | 3.10 | 0.856 |
| 100 | 0.355 | 3.77 | 3.42 | 0.906 |
| 200 | 0.128 | 26.30 | 26.17 | **0.995** |
| 500 | 0.081 | 21.01 | 20.93 | **0.996** |

`C+R″` is the **minute difference of two large, nearly-equal** energies — `neg/pos → 1`.
This is the **worst-case structure for a proof**: not "the Fiedler dodges the negative
cone" (avoidance) but "huge positive and negative contributions almost exactly cancel."

**Contrast with the actual-triangle operator** `M = λ₂Q − L_t` (the *true* B slack,
`fᵀMf = λ₂(fᵀQf−S²/m) − fᵀL_tf`):

| `n` | B2′ slack `C+R″` (margin) | true-triangle B slack (margin) |
|---|---|---|
| 50 | 0.52 (0.118) | 1.17 (0.264) |
| 100 | 0.35 (0.085) | 0.96 (0.228) |
| 200 | 0.13 (0.031) | 2.79 (0.679) |
| 500 | 0.08 (0.020) | 0.75 (0.185) |

The true-triangle margin stays bounded away from 0 (0.18–0.68, noisy); the
min-degree-relaxed margin **decays to 0**. The relaxation `W₁ = Σ(min(d_a,d_b)−1)(Δf)²`
inflates the LHS over `fᵀL_tf` by `~1.2×` (up to 3×), and *that inflation is exactly what
eats the asymptotic margin*. **The min-degree relaxation — not Conjecture B itself — is
what is asymptotically tight on deg2+dense.** (The actual-triangle operator retains the
600× avoidance structure seen corpus-wide.)

---

## TASK B — convergence rate of the margin

Margin `1 − |C|/R″` vs `n` (deg2+dense, `q=0.65`):

| `n` | margin | `C+R″` | `R″` |
|---|---|---|---|
| 30 | 0.609 | 0.882 | 1.453 |
| 100 | 0.341 | 0.318 | 0.934 |
| 200 | 0.179 | 0.145 | 0.811 |
| 500 | 0.111 | 0.082 | 0.745 |
| 1000 | 0.063 | 0.046 | 0.724 |
| 1500 | 0.052 | 0.037 | 0.714 |

**Fits:** power `a·n^{−β}` with **β = 0.663, R² = 0.986** — far better than logarithmic
(R² 0.56) or exponential (R² 0.65). So the margin **→ 0 polynomially**, `~ n^{−2/3}`.
Separately, `R″ → ` constant `≈ 0.71` (down from 1.45) and `C+R″ → 0 ~ n^{−2/3}`, i.e.
`|C| → R″`. The slack closes at a definite polynomial rate — never reaching 0 at finite
`n` (B2′ holds), but with no uniform lower bound.

---

## TASK C — aggregation-loss anatomy (looseness, not cancellation)

The per-vertex bound `−C(l) ≤ λ₂ d_l f_l²` aggregates to `−C ≤ λ₂ M_neg`
(`M_neg = Σ_{C(l)<0} d_l f_l²`), which overshoots `R″` ~6×. Decomposing the loss
`λ₂ M_neg/|C| = [per-vertex looseness] × [neg-only/|C|]`:

| `n` | #`C(l)>0` / #`C(l)<0` | `Σ\|C(l)\|/\|C\|` | `λ₂M_neg/\|C\|` = loose × cancel |
|---|---|---|---|
| 100 | 80 / 19 | 1.21 | 7.05 = **6.38** × 1.10 |
| 200 | 79 / 120 | 1.29 | 7.09 = **6.19** × 1.15 |
| 500 | 339 / 159 | 1.09 | 6.68 = **6.39** × 1.04 |

**The 6× loss is overwhelmingly per-vertex looseness (~6.4), not sign cancellation
(~1.1).** Why: the negativity of `C` is **concentrated at the single degree-2 vertex**
(the most-negative `C(l)` is always at the min-degree vertex, `d_l=2`, at every `n`),
while `M_neg = Σ_{C(l)<0} d_l f_l²` sums `λ₂ d_l f_l²` over *many* high-degree dense
vertices (120 of them at `n=200`) whose `C(l)` is tiny but whose `d_l f_l²` is not. So the
bound charges large `d_l f_l²` to dense vertices that contribute ~nothing to `C`.

- **No clean degree split for the sign of `C(l)`**: `C(l)>0` and `C(l)<0` vertices have
  essentially equal mean degree (e.g. 130.4 vs 128.4 at `n=200`) — the sign is not a
  degree threshold; only the *one* degree-2 vertex is robustly, dominantly negative.
- Mild sign cancellation (`Σ|C(l)|/|C| ≈ 1.1–1.3`) exists but is second-order.

**Implication for a proof:** isolate the **degree-2 vertex's term `C(0)`** (which carries
the negativity) and bound it against `R″` directly; treat the dense bulk as net ≈ 0.
Spreading a per-vertex bound over all low vertices is structurally doomed (charges the
dense bulk).

---

## Synthesis

- **`C+R″ ≥ 0` on deg2+dense is near-cancellation, not avoidance** (`neg/pos → 0.996`) —
  the hardest possible structure, and it is an artifact of the **min-degree relaxation**:
  the actual-triangle B slack keeps a healthy margin (0.18–0.68) and the 600× avoidance.
- **The margin decays `~ n^{−2/3}`** (power law, R² 0.99); `R″ →` const, `|C| → R″`.
- **The negativity localizes at the single degree-2 vertex**; the per-vertex bound's 6×
  loss is looseness from charging dense vertices, not cancellation.

**Two strategic takeaways:**
1. **For Conjecture B itself, drop the min-degree relaxation on this regime** — work with
   the actual-triangle operator `M = λ₂Q − L_t`, which is *not* asymptotically tight on
   deg2+dense (it has the avoidance structure). B2′ is a convenient triangle-free
   reduction but a *strictly worse* inequality here; proving B may be easier than B2′.
2. **For B2′, the proof must be a two-part argument**: the degree-2 vertex term `C(0)`
   bounded exactly against `R″` (the binding piece), plus a near-cancellation argument for
   the dense bulk — not a uniform per-vertex bound.

### Caveats
`λ₂`, `f`, `K`/`M` spectra numerical. deg2+dense, `q=0.65`, to `n=1500` (TASK B) / `n=500`
(A, C); 2–6 samples/size. The true-triangle margins are noisy across samples (0.18–0.68)
but do not trend to 0, unlike the B2′ margin (clean `n^{−2/3}`). B2′ holds at every finite
`n`; it is the asymptotic margin, not positivity, that vanishes.
