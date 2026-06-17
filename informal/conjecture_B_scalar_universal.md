# Conjecture B — universality of the scalar reduction `fᵀDf + Σ_H f² ≥ λ₂ + S²/m`

Test whether the deg2+dense scalar reduction generalises. `v₀ = argmax f_v²`;
`H` a carrier set; `margin_H = (fᵀDf + Σ_{v∈H} f_v²) − (λ₂ + S²/m) = Σ_{v∈H} f_v² − R`,
where `R = λ₂ + S²/m − fᵀDf = Required/λ₂`. Code:
[`conjecture_B_scalar_universal.py`](../conjecture_B_scalar_universal.py).

**Headline: the scalar reduction is deg2+dense-specific, NOT universal.** It holds on
deg2+dense (`R < 1`, even `H = {v₀}` suffices) but **fails on lollipops**: when the Fiedler
spreads (`R > 1`, 67% of lollipops) the inequality `Σ_H f² ≥ R` is **unsatisfiable**
(`Σf² ≤ 1 < R`), so *no* carrier set `H` — not even `H = V` — can close it. The premise
`Deficit ≈ λ₂·Σ_H f²` (single/few carriers) is the deg2+dense special case and breaks where
the carrier mechanism broke (lollipops). **`Required > 0` itself is rare** — among barbells,
appendices, cliques, and 200 random graphs, *none* had `Required > 0`.

---

## TASK 1 — universality across `Required > 0` families

| family | #(`Req>0`) | `R` range | `R>1` | `m_top1>0` | `m_top5>0` | `m_H80>0` | `m_H90>0` |
|---|---|---|---|---|---|---|---|
| deg2+dense | 4 | 0.42–0.63 | 0% | **100%** | 100% | 100% | 100% |
| lollipop | 6 | 0.45–**4.09** | **67%** | 17% | 33% | 33% | 33% |
| barbell | 0 | — | — | — | — | — | — |
| random (200) | 0 | — | — | — | — | — | — |
| appendix | 0 | — | — | — | — | — | — |

- **deg2+dense:** `R < 1`; `f_{v₀}² ≈ 1 ≥ R`, so the **single-vertex** `H = {v₀}` already
  gives `margin > 0` on all. The reduction is exact and tight here.
- **lollipop:** `R` ranges to **4.09**. Since `margin_H = Σ_H f² − R ≤ 1 − R`, **any** `R > 1`
  forces `margin_H < 0` for **every** `H` (mass is capped at `‖f‖² = 1`). So the scalar
  inequality is *false*, no matter the carrier set — yet B still holds (via the actual
  `Deficit = λ₂fᵀDf − T`, which is *not* `λ₂·Σ_H f²` here).
- **`Required > 0` is rare:** clique-based families (barbell, appendix, chain) and 200
  random `G(n,p)` all have `Required ≤ 0` (B-trivial via the aggregate Poincaré). Only
  deg2+dense and lollipops realise `Required > 0`.

**No `H` closes all `Required > 0` graphs.** Larger `H` helps on the mild (`R<1`) lollipop
(`H90` works, `top1` doesn't) but cannot help once `R > 1`.

## TASK 3 — lollipop analysis

| lollipop | `f_{v₀}²` | `\|H80\|` | `R` | `m_top1` | `m_H90` |
|---|---|---|---|---|---|
| `m=20, L=5` | 0.322 | 4 | 0.78 | −0.46 | **+0.13** |
| `m=20, L=10` | 0.164 | 13 | **1.47** | −1.30 | −0.56 |
| `m=50, L=10` | 0.176 | 7 | **4.09** | −3.91 | −3.19 |

- The Fiedler is **spread** (`f_{v₀}² = 0.16–0.32 ≪ 1`), and `|H80| > 1` (4–13 vertices) —
  no single carrier.
- For the *mild* lollipop (`L=5`, `R<1`) the **cumulative** `H90` version closes
  (`+0.13`) while `top1` fails (`−0.46`) — so there the carrier-mass version is needed.
- For *long* lollipops (`L=10`, `R>1`) the inequality fails for **all** `H` (the mass cap).
  B holds anyway because `Deficit ≫ λ₂·Σf²` (the clique apices carry it), so the
  scalar premise is simply wrong here.

Using the eigen-equation at each path vertex (`(2 − λ₂)f_v = f_{v−1}+f_{v+1}` along the
path, `λ₂` tiny) shows the path Fiedler is a near-linear ramp — many vertices share the
mass — which is exactly why `f_{v₀}²` is small and a single-carrier reduction is impossible.

## TASK 2 — algebraic reduction on deg2+dense (and what it needs)

Substituting `λ₂ → d_{v₀} = 2`, `S²/m → 2q·f_{v₀}²`, `fᵀDf = d_{v₀}f_{v₀}² +
Σ_{v≠v₀} d_v f_v²` into `fᵀDf + f_{v₀}² ≥ λ₂ + S²/m`:

`(d_{v₀}+1)f_{v₀}² + Σ_{v≠v₀} d_v f_v² ≥ d_{v₀} + 2q·f_{v₀}²`
`⟺ (3 − 2q)·f_{v₀}² + Σ_{v≠v₀} d_v f_v² ≥ 2`   (`d_{v₀}=2`)
`⟶ (3 − 2q) + Σ_{v≠v₀} d_v f_v² ≥ 2`   (`f_{v₀}² → 1`)
`⟺ Σ_{v≠v₀} d_v f_v² ≥ 2q − 1.`

So on deg2+dense the scalar inequality reduces to the **residual dense degree-mass bound**
`Σ_{v≠v₀} d_v f_v² ≥ 2q − 1`. **This is NOT manifestly positive from the eigen-equation +
`‖f‖=1` + `f⊥1` alone** — the eigen-equation at `v₀` only fixes `λ₂` and the *first* moment
of the neighbours; `Σ_{v≠v₀} d_v f_v²` is a *second*-moment quantity of `f` on the dense
bulk, governed by how the Fiedler distributes there — i.e. by the **minimality of `λ₂`** (the
smoothness of `f`), not by the bottleneck equation. So even the deg2+dense scalar inequality
is *not* purely algebraic; its one non-trivial input is the dense second-moment, which is a
minimality-level fact.

## TASK 4 — the residual `Σ_{v≠v₀} d_v f_v²` on deg2+dense

| `n` | `Σ_{v≠v₀} d_v f_v²` | `≥ 2q−1 = 0.30`? |
|---|---|---|
| 50 | 0.694 | ✓ |
| 100 | 0.667 | ✓ |
| 200 | 0.659 | ✓ |
| 500 | 0.652 | ✓ |
| 1000 | 0.651 | ✓ |

Converges to **≈ 0.65** (`> 0.30`, margin 0.35). So the deg2+dense scalar inequality holds
with a stable margin, reducing to this single converging second-moment bound.

---

## Synthesis

- **The scalar reduction `fᵀDf + Σ_H f² ≥ λ₂ + S²/m` is deg2+dense-specific.** It is exact
  and tight there (`R < 1`, single carrier), and reduces to `Σ_{v≠v₀} d_v f_v² ≥ 2q−1` (a
  minimality-level second-moment fact, → 0.65).
- **It is not universal.** Lollipops with spread Fiedler have `R > 1`, making the inequality
  *unsatisfiable* (`Σf² ≤ 1`), for every carrier set `H`. The cumulative `H80/H90` version
  rescues only the mild (`R<1`) cases. B still holds on lollipops, but via the true
  `Deficit = λ₂fᵀDf − T` (clique-carried), not the scalar/carrier surrogate.
- **`Required > 0` is rare** (only single-bottleneck deg2+dense and path-bottleneck
  lollipops among everything tried); clique multi-bottlenecks and random graphs are all
  B-trivial (`Required ≤ 0`).

So the `Required > 0` regime splits *again* into two structurally different sub-cases
(single-vertex bottleneck: scalar reduction with `R<1`; path bottleneck: `R` can exceed 1,
needing the genuine `Deficit ≥ Required`), with no single scalar inequality covering both —
consistent with every prior round. The recurring need is a **minimality-based bound on the
Fiedler's second moment / smoothness**, which appears even in the cleanest (deg2+dense)
reduction via `Σ_{v≠v₀} d_v f_v² ≥ 2q−1`.

### Caveats
`λ₂`, `f` numerical. `Required > 0` found only on deg2+dense (q=0.65, n≤500) and lollipops
(m∈{20,50}, L∈{3,5,10}); 200 random + barbell/appendix/chain gave none. `R`, margins exact;
the `2q−1` reduction uses the `n→∞` limits (`λ₂→2`, `S²/m→2q`, `f_{v₀}²→1`). B (`Deficit ≥
Required`) holds on every graph tested.
