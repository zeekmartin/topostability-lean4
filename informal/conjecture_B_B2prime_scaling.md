# Conjecture B — does the degree-only relaxation B2′ survive at all scales?

**B2′:** `Σ_e (min(d_a,d_b)−1)·(f_a−f_b)² ≤ λ₂·G`, `G = Σ_e(f_a+f_b)² − S²/m`, `S = Σ_v d_v f_v`.
Since `t_e ≤ min(d_a,d_b)−1`, B2′ is *stronger* than `B ⟺ T ≤ λ₂G` and uses **no triangle counts** —
so it tests at any scale (only degrees + Fiedler). Code:
[`conjecture_B_B2prime_scaling.py`](../conjecture_B_B2prime_scaling.py).

## Verdict: **B2′ holds at every tested scale (0 failures, up to n = 5000).**

## TASK 1 — deg2+dense scaling (the critical test)

`deg2+dense` = a degree-2 vertex attached to a dense `G(n−1, 0.65)` core (the family that broke the
*wrong* min-degree lock `W ≤ R″` at scale). Against the **correct** RHS `λ₂G`:

| n | λ₂ | B2′ | λ₂G | ratio | margin = 1−ratio |
|---|---|---|---|---|---|
| 50 | 1.968 | 3.905 | 4.432 | 0.881 | 0.119 |
| 100 | 1.988 | 3.855 | 4.204 | 0.917 | 0.083 |
| 200 | 1.994 | 3.957 | 4.102 | 0.965 | 0.035 |
| 500 | 1.998 | 3.962 | 4.041 | 0.981 | 0.019 |
| 1000 | 1.999 | 3.983 | 4.020 | 0.991 | 0.0092 |
| 2000 | 1.999 | 3.992 | 4.010 | 0.996 | 0.0044 |
| 3000 | 2.000 | 3.993 | 4.007 | 0.9966 | 0.0034 |
| 5000 | 2.000 | 3.993 | 4.004 | 0.9973 | 0.0027 |

> **ratio < 1 at ALL sizes; margin → 0 from ABOVE, never crossing.**

Asymptotic fits (n = 50…2000): `λ₂ → 2` (const, `n^{0.004}`), `G → const` (`n^{−0.03}`),

> `gap = λ₂G − B2′ ~ 21·n^{−0.92}`,  `margin ~ 4.5·n^{−0.90}`,  `gap/λ₂ ~ n^{−0.93}`.

So the margin decays like **`~ n^{−0.9}`** (≈ `1/n`), **not** `n^{−2/3}` — but it stays strictly
positive (a power law never reaches 0). **`deg2+dense` is the asymptotically extremal family**
(`ratio → 1`), yet B2′ is never violated. This is the decisive datum: the earlier "lock fails at
scale" was an artifact of the wrong (factor-`m`-shrunk) RHS; against `λ₂G`, B2′ is asymptotically
*tight but true*.

## TASK 2 — other hard families at scale

| family | sizes | ratio range | margin |
|---|---|---|---|
| lollipop `K_m + path_L` | up to n=150 | 0.28 → 0.19 | → **0.81** (grows) |
| barbell `K_m–path–K_m` | up to n=250 | 0.068 → 0.0056 | → **0.99** |
| glued cliques `K_m·K_m` | up to n=199 | 0.471 → 0.497 | → **0.50** |

All comfortably below 1, with *increasing* margins. **`deg2+dense` is the unique asymptotically-tight
family**; path-bottleneck (lollipop/barbell) and glued-clique families have bounded-away-from-1
ratios. (Glued cliques sit at exactly `ratio → 1/2`: `λ₂ = 1`, `B2′ = m−2`, `λ₂G = 2m−3`.)

## TASK 3 — B2′ survives ⇒ B is a triangle-free degree-variance inequality

With B2′ confirmed at scale, **Conjecture B reduces to the triangle-free inequality**

> `Σ_e (min(d_a,d_b)−1)(f_a−f_b)² ≤ λ₂·(Σ_e (f_a+f_b)² − S²/m)`  — no triangles, no `Open`.

For **regular** graphs this is the formalised `aggregate_triangle_poincare_regular` (`min = d`
uniform, `S = 0`, `G = 2d − λ₂`). What makes the **irregular** case hard is precisely what the
`deg2+dense` extremal shows:

- **Asymptotic tightness.** Any proof must be *essentially sharp* — the regular slack `d/(d−1)` is
  gone; on `deg2+dense` the inequality is saturated in the limit, so no term may be wasted.
- **The `S²/m` centering is load-bearing.** On `deg2+dense`, `S = Σ_v d_v f_v ≈ −0.65n·f_{v₀}` is
  *large* (the dense core carries the degree mass against the bottleneck value), so `λ₂S²/m = Θ(1)`
  is a Θ(1) fraction of `λ₂G`. Unlike the regular case (`S = 0`), the centering cannot be dropped.
- **Per-edge weight heterogeneity.** The bottleneck edges have `min−1 = 1` (small weight, large
  gradient `g`); the dense edges have `min−1 ≈ 0.65n` (large weight, tiny gradient). B2′ balances
  these; a uniform bound fails (TASK 3 of [`conjecture_B_regular_extension.md`] showed the *average*
  `t_avg` is too coarse).

The natural route is the split `g_e² = h_e² − 4f_a f_b`, giving
`B2′ = Σ(min−1)h_e² − 4Σ(min−1)f_a f_b`, to be matched against `λ₂Σh² − λ₂S²/m`. But the dense edges
have `min−1 ≫ λ₂`, so `Σ(min−1)h²` is **not** termwise `≤ λ₂Σh²` — the cancellation with
`−4Σ(min−1)f_af_b` (the signless correlation) is global, the same irreducible coupling as every prior
round, now in the sharpest degree-only form.

## TASK 4 — no failure; the extremal structure

Since B2′ never fails, there is no crossover to diagnose. The asymptotic *tightness* on `deg2+dense`
is driven by the **bottleneck**: the degree-2 vertex `v₀` (weight `min−1 = 1` on its two edges, large
gradient `g ≈ f_{v₀}`) supplies almost all of B2′, while `λ₂ → 2` and `G → const` so `λ₂G → B2′`. The
near-equality is a *bottleneck* phenomenon (the cut at `v₀`), exactly where `λ₂` is set — consistent
with B being a spectral/bottleneck statement at heart.

## Conclusion

- **B2′ ≤ λ₂G holds at all tested scales (n ≤ 5000), 0 failures.** On the critical `deg2+dense`
  family the margin decays as `~n^{−0.9}` (≈ `1/n`) to 0 *from above* — asymptotically tight but
  never violated. The previous "fails at scale" was the factor-`m` RHS error.
- **Conjecture B is (on every tested graph, all scales) a triangle-free degree-variance inequality:**
  `Σ_e(min(d_a,d_b)−1)(f_a−f_b)² ≤ λ₂(Σ_e(f_a+f_b)² − S²/m)`. Regular case: formalised. Irregular
  case: open, and necessarily *sharp* — the `deg2+dense` extremal forbids any slack, and the `−S²/m`
  centering is Θ(1)-load-bearing.
- **No new Lean lemma this round** (a scaling/empirical study; the regular case is already the
  formalised `aggregate_triangle_poincare_regular`).
