# Conjecture B — the asymptotic mechanism of `gap = λ₂G − B2′` on deg2+dense

Two models of "a degree-2 vertex `v₀` attached to a dense core":
- **q=1** — `v₀` attached (at vertices 0,1) to a **complete** core `K_{n−1}` (deterministic, exact);
- **q<1** — `v₀` attached to `gnp(n−1, 0.65)` (the random deg2+dense).

Code: [`conjecture_B_asymptotic_mechanism.py`](../conjecture_B_asymptotic_mechanism.py).

## Headline — the q=1 model has an EXACT, manifestly positive gap

For `v₀` attached to `K_{n−1}` the Fiedler pair is solvable in closed form (verified to machine
precision):

> **`λ₂ = 2` exactly**;  `f_0 = f_1 = 0` (the Fiedler **vanishes at the two attachment vertices**);
> `f_{v₀} = −√((n−3)/(n−2))`, `f_bulk = 1/√((n−3)(n−2))`.

Then `B2′ = Σ_e h_e²` and **`gap = λ₂G − B2′ = Σ_e h_e² − 2S²/m = 10(n−3)/m`** (exact), where
`h_e = f_a+f_b`, `S = Σ_v d_v f_v`, `m = |E| = (n−1)(n−2)/2 + 2`. So **`gap ~ 20/n → 0⁺`**, never
zero — a complete, closed-form proof of B for the whole family `deg2 + K_{n−1}`.

**Manifest positivity.** `gap = Σh² − 2S²/m = 2(n−3)²z²·(2 − (n−4)²/m)` with `z² =
1/((n−3)(n−2))`, and

> `2 − (n−4)²/m = (2m − (n−4)²)/m`,  `2m − (n−4)² = (n−1)(n−2)+4 − (n−4)² = 5(n−2) > 0`.

So positivity reduces to **`2m ≥ (n−4)²`** (edge count beats the squared degree-gap), with surviving
margin `5(n−2)` ⇒ `gap = 10(n−3)/m`. It is `(positive)·(positive)`, no hidden cancellation.

## TASK 1 — leading terms and corrections

**q=1 (exact):** `λ₂ = 2`, `B2′ = Σh² = 4(n−3)²z² → 4`, `Σh² → 4`, `S²/m → 2`, `fᵀDf =
(3n−8)/(n−2) → 3`, `gap = 10(n−3)/m → 20/n`.

**q=0.65 (random, fitted):**

| quantity | scaling | limit |
|---|---|---|
| `ε₁ = 2 − λ₂` | `~ 1.9·n^{−1.08}` | `0⁺` |
| `gap` | `~ 21·n^{−0.92}` | `0⁺` |
| `B2′_bottleneck`, `B2′_dense` | `~ const` | `→ 2, → 2` (sum `B2′ → 4`) |
| `Σh²_bottleneck`, `Σh²_dense` | `~ const` | `→ 2.0, → 1.30` (sum `→ 3.30`) |
| `S²/m` | `~ const` | `→ 1.30` |
| `1 − f_{v₀}²` | `~ 1.2·n^{−1.03}` | `0⁺` |

The bottleneck edges carry the `O(1)` energy (`B2′_bott → 2`, `Σh²_bott → 2`); the dense edges
contribute the rest. `f_{v₀} → ±1` (the Fiedler concentrates on the deg-2 vertex).

## TASK 2 — which terms cancel (`gap = R″ + C`)

- **q=1:** `C = 0` **exactly** (verified `~10⁻¹⁴`). Because `f_0 = f_1 = 0`, every higher-degree-
  endpoint term at the attachment vertices vanishes, and all other edges have equal-degree endpoints;
  the degree-gradient `C` collapses entirely. So `gap = R″ = Σh² − 2S²/m` — a *pure spectral term*,
  no cancellation.
- **q<1 (random):** `C ≠ 0`. `R″ → 0.72`, `C → −0.68`, and `gap = R″ + C → 0⁺` is their **near-
  cancellation** (both `O(1)`). The q=1 simplification (`C = 0`) is destroyed by `f_0, f_1 ≠ 0`.

So the surviving `O(1/n)` remainder is: **q=1** — all of `R″` (`= 10(n−3)/m`); **q<1** — the residual
of the `R″`↔`C` near-cancellation (no closed form).

## TASK 3 — manifestly positive form

**Yes, for q=1:** `gap = Σh² − 2S²/m = G − S²/m = 10(n−3)/m`, manifestly positive via the integer
identity `2m − (n−4)² = 5(n−2) > 0`. It is a *difference of explicit positives* whose value is the
clean `10(n−3)/m`. (Equivalently `gap = m·Var_E(h) − S²/m` with `Var_E(h)` the edge-lift variance.)

**For q<1: no manifestly positive closed form** — `λ₂ ≠ 2` and `B2′ ≠ Σh²`, so `gap` is the
`R″ + C` near-cancellation. The hardness is exactly this: the q=1 structural collapse (`C=0`,
`λ₂=2`, `f` zero at attachments) is special; generic incompleteness reintroduces the signed
degree-gradient `C` that nearly cancels the spectral `R″`.

## TASK 4 — does the mechanism generalize?

**No — the closed form is family-specific.** `gap = Σh² − 2S²/m` is exact **only** when `λ₂ = 2` *and*
`B2′ = Σh²` (both hold for q=1, both fail otherwise):

| family | `gap` | `Σh² − 2S²/m` | match |
|---|---|---|---|
| deg2 + K(q=1) | 0.100 | 0.100 | **YES** |
| deg2+dense q=.65 | 0.145 | 0.813 | no (`λ₂=1.994`, `B2′−Σh²=0.66`) |
| lollipop(100,50) | 0.006 | −41.0 | no (`λ₂≈0`, `B2′−Σh²=−51.6`) |
| barbell(50,20) | 0.164 | 92.6 | no |

The **universal** objects are the **variance** `G = Σh² − S²/m` and the **deficit** `S²/m`; the q=1
mechanism (`Σh² ≥ 2S²/m` via `2m ≥ (n−4)²`) is the special, exactly-solvable face of the general
`B2′ ≤ λ₂G`. For general graphs the positive surviving term has no closed form (it is the conjecture).

## TASK 5 — the eigenvalue correction `ε₁ = 2 − λ₂`

The `v₀`-row of `Lf = λ₂f` is `(2 − λ₂)f_{v₀} = f_a + f_b` (`a,b` the two neighbours) — verified
exactly. Hence `ε₁ = 2 − λ₂ = (f_a + f_b)/f_{v₀}`.

- **q=1:** `f_a = f_b = 0` ⇒ **`ε₁ = 0` exactly** (`λ₂ = 2`).
- **q<1:** `f_a + f_b ≈ 2·(mean dense value) ≈ −2 f_{v₀}/(n−1)` (from `f ⊥ 1`, `f_{v₀} ≈ 1`), so
  **`ε₁ ≈ 2/(n−1) ~ 1.9·n^{−1.08}`** (fitted `c ≈ 1.9 ≈ 2`). The correction is `Θ(1/n)`, set by how
  much Fiedler mass the dense core carries against the bottleneck value.

`ε₁` enters `gap` through `R″ = λ₂(fᵀDf − λ₂ + 1 − S²/m)` (the `λ₂ = 2 − ε₁` factor) and through
`B2′`; at q=1 (`ε₁ = 0`) these combine to the exact `10(n−3)/m`.

## Conclusion

- **q=1 deg2+`K_{n−1}`: B is proved in closed form** — `gap = 10(n−3)/m > 0`, manifestly positive
  (`2m − (n−4)² = 5(n−2)`), `C = 0`, `λ₂ = 2`. The Fiedler vanishing at the attachments makes
  everything collapse.
- **The asymptotic margin `~ 20/n`** is exactly the `5(n−2)` surviving term over `m ~ n²/2`.
- **q<1 is genuinely harder:** incompleteness reintroduces `C` (the signed degree-gradient), and
  `gap = R″ + C` is a near-cancellation of `O(1)` terms with no closed form — the universal
  obstruction, of which q=1 is the one exactly-solvable instance.

## Lean
No new lemma: the q=1 result is a specific-family closed-form computation (would need the
`deg2+K_{n−1}` graph family and its explicit Fiedler pair in Lean), and it yields no new *general*
exact identity beyond the already-formalised `gap = λ₂G − B2′` decomposition (`B2prime_min_decomp`,
`quadForm_*`, `degAssort_covariance`). The general manifestly-positive form remains open (it is B).
