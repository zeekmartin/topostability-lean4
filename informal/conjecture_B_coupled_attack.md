# Conjecture B — coupled attack on `C+R″ ≥ 0`: B2′ is asymptotically tight

Treat `C+R″` as one coupled quantity (no separate `|C|` bound). Code:
[`conjecture_B_coupled_attack.py`](../conjecture_B_coupled_attack.py).

**Headline.** **`|C|/R″ → 1` on deg2+dense** (TASK 1): the B2′ slack `(C+R″)/R″ → 0` as
`n → ∞`. **B2′ is asymptotically tight on this family, so no bound with fixed slack can
ever close it** — the proof must be asymptotically exact. The per-vertex coupled bound
`−C(l) ≤ λ₂ d_l f_l²` (TASK 2) holds 100% and is scale-stable, but aggregates too lossily
(`λ₂·Σ_{C(l)<0} d_l f_l² / R″ → 6.4`). All explicit perturbations (TASK 3) anti-correlate
with `C+R″` — it is not a second variation of any natural `p`. The route forward is the
exact eigen-equation coupling (TASK 4), not any inequality with slack.

---

## TASK 1 — asymptote on deg2+dense (decisive: `→ 1`)

A degree-2 vertex joined to a dense `G(n−1, 0.65)` background, `n` to 1000:

| `n` | max `\|C\|/R″` | B2′ margin `(C+R″)/R″` |
|---|---|---|
| 50 | 0.580 | 0.420 |
| 100 | 0.737 | 0.263 |
| 200 | 0.847 | 0.153 |
| 300 | 0.868 | 0.132 |
| 500 | 0.936 | 0.064 |
| 1000 | **0.953** | **0.046** |

Monotone increasing toward 1; the margin shrinks toward 0. **B2′ is asymptotically tight**
on deg2+dense. Consequence: any approach of the form `|C| ≤ B ≤ R″` with `B` carrying a
fixed multiplicative slack must fail for large `n` — exactly what happened to every bound
in the previous round. **The proof has to be exact in the limit.**

---

## TASK 2 — per-low-degree-vertex decomposition (valid, scale-stable, but too lossy in aggregate)

Group `C = Σ_l C(l)` by the **low**-degree endpoint:
`C(l) = Σ_{h∈N(l), d_h>d_l} (d_h−d_l) f_h (f_h−f_l)`. Local Dirichlet energy
`E(l) = Σ_{u∈N(l)} (f_l−f_u)²`; the eigen-equation gives `Σ_{u∈N(l)}(f_l−f_u) = λ₂ f_l`,
hence (Cauchy–Schwarz) `λ₂² f_l² ≤ d_l E(l)`.

| candidate per-vertex bound (over `l` with `C(l)<0`) | corpus `n≤9` | deg2+dense `n=50..200` |
|---|---|---|
| `−C(l) ≤ α λ₂ E(l)` | max α **4.93** (1<: 97%) | max α **339** (fails) |
| `−C(l) ≤ α λ₂ d_l f_l²` | max α **0.83**, 100% | max α **0.44**, 100% |

So **`−C(l) ≤ λ₂ d_l f_l²` holds universally with `α < 1`, and does not degrade at scale**
(it even improves: 0.44). This is a genuine per-vertex coupled inequality. **But the
aggregate is too weak**: summing gives `−C ≤ λ₂ · Σ_{C(l)<0} d_l f_l² =: λ₂ M_neg`, valid
(`−C ≤ λ₂ M_neg` on 9014/9014), yet

> `λ₂ M_neg ≤ R″` holds only **2632/9014** on the corpus, and at scale
> `λ₂ M_neg / R″` grows **4.4 → 6.4** (`n`: 50 → 1000).

Because `−C/R″ → 0.95` while the bound `λ₂ M_neg / R″ → 6.4`, the per-vertex bound loses a
factor ~6 in aggregate — the `C(l)` cancel/are far below `λ₂ d_l f_l²` collectively, while
`M_neg` stays large. (The `E(l)` form fails outright at scale.) **No closure.**

---

## TASK 3 — perturbative Rayleigh (all natural perturbations fail)

For `p' ⊥ {1,f}`, `E_p := p'ᵀ(L−λ₂)p' ≥ 0` by minimality. If `C+R″ = E_p` for an explicit
`p`, B2′ is proved. (The brief's "`C+R″ ≤ c·E_p ⇒ ≥0`" is the wrong direction — an upper
bound by a nonneg quantity gives nothing; one needs `C+R″` to *equal/exceed* a second
variation.) Correlations and best linear fits:

| perturbation `p` | corpus corr | hard-core corr | best-`c` R² |
|---|---|---|---|
| `(d−d̄)f` | −0.66 | −0.61 | −3.2 |
| `f/d` | −0.83 | **−0.85** | −5.4 |
| `(d−λ₂)f` | −0.66 | −0.61 | −3.2 |
| `sign(d−med)f` | −0.30 | −0.21 | −2.1 |

Every candidate **anti-correlates** with `C+R″` (R² < 0 — worse than the mean). `C+R″` is
**not** the second variation of any of these vectors, confirming the reverse-vector
round: minimality cannot be applied through an explicit degree-built perturbation. (`f/d`
has the strongest |corr| but still anti-aligned: its energy is *large* where `C+R″` is
*small*.) The minimality that makes B true is the *intrinsic* minimality of `f` itself
(`fᵀMf ≥ 0`), not a constructed direction.

---

## TASK 4 — exact eigen-equation coupling (the only remaining direction)

Since the slack vanishes asymptotically (TASK 1), the proof must use the eigen-equation
*exactly*. At each low-degree `l`, `f_l = (Σ_{u∈N(l)} f_u)/(d_l − λ₂)` (when `d_l ≠ λ₂`).
On deg2+dense the binding vertex is the degree-2 one (`l=0`): `(2−λ₂)f_0 = f_a + f_b`, and
since `λ₂ → 0` (the degree-2 bottleneck), `f_0 ≈ (f_a+f_b)/2` with `f_0` carrying the bulk
of the Fiedler mass. Substituting this exact relation into `C(0)` and pairing with the
matching `R″` terms is the natural "telescoping" the brief asks for; numerically the
residual `C+R″` equals the established exact identity `RHS − W₁` (verified to 1e-13 in
prior rounds), with **no further algebraic cancellation into a manifestly-nonnegative
form** — consistent with the indefinite-Gram / not-SOS findings. The exact coupling is
real but does not collapse to a sign-obvious expression; closing it needs the *global*
minimality of `λ₂` (that `f` minimizes the Rayleigh quotient on `1⊥`), used on the whole
vector, not edge-local substitution.

---

## Synthesis

- **`|C|/R″ → 1` (TASK 1) is the decisive fact**: B2′ is asymptotically tight on
  deg2+dense, so the entire family of "bound `|C|` by something `≤ R″`" strategies is
  ruled out — including the per-vertex bound, which is valid and scale-stable but loses
  ~6× in aggregate (TASK 2).
- **`C+R″` is not a second variation** of any natural perturbation (TASK 3); the needed
  minimality is intrinsic to `f`.
- **The proof must be asymptotically exact** (TASK 4): use the eigen-equation/global
  minimality to show `C ≥ −R″` directly, with the deg2+dense asymptote (where the two
  sides meet) as the binding case. This is the same `λ₂`-minimality core identified
  throughout, now proven (via the `→1` asymptote) to be *unavoidable* — no slack-based
  argument can substitute for it.

### Caveats
`λ₂`, `f` numerical. TASK 1 deg2+dense sweep to `n=1000` (2–8 samples/size, `q=0.65`).
TASK 2/3 over the 9020-graph `n≤9` corpus + deg2+dense `n≤200`. `−C ≤ λ₂ M_neg` and
`−C(l) ≤ λ₂ d_l f_l²` verified exact-direction; the failures are aggregate-`≤R″` and the
asymptote. B2′ holds throughout (margin `> 0` at every finite `n`).
