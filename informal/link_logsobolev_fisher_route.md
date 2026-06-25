# Link-based log-Sobolev / Fisher route for `aggregate_triangle_poincare`

**Target** (undirected normalization): `T = Σ_e t_e (f_a−f_b)² ≤ λ·degQuad`,
with `degQuad = Σ_v d_v f_v²`, `t_e = |N(a)∩N(b)|`, `f` the unit Fiedler. (The Lean form
`triEnergy ≤ 2λ·degQuad` is this ×2; `triEnergy` is the ordered sum.)

**Verdict: the link-averaging route does not work.** TASKs 1 and 3 are **circular** (`T ≤ 4T`,
factor confirmed `= 4.000` on every graph). TASK 2 fails because the local triangle variance is a
**global** quantity (spread ×60000 within a single local-degree class). TASK 4's normalized
energies are bounded but provide **no mechanism** to recover the aggregate. The root cause is the
same **Hadamard obstruction** already on record: `T = fᵀ(D_t − A∘A²)f`, and its smallness comes
from Fiedler *flatness on dense regions* — a global spectral fact that no local inequality captures.

Numerics: `link_logsobolev_fisher_route.py`, 13-graph corpus (cliques, dumbbells/bottlenecks,
G(n,p), deg2d, twin, Barabási–Albert, Watts–Strogatz, triangular lattice).

---

## CHECK FIRST (TASK 1 & 3) — CIRCULAR, confirmed analytically and numerically

The link expansion is an **identity**, not a bound. Summing `t_e g_e²` over edges and grouping by
triangle:

```
T = Σ_e t_e (f_a−f_b)²  =  Σ_{(e=ab, c∈Link(e))} g_ab²  =  Σ_{triangles {a,b,c}} (g_ab² + g_bc² + g_ca²).
```

Each triangle contributes **all three** of its squared edge-gaps. Now apply
`(f_a−f_b)² ≤ 2[(f_a−f_c)² + (f_c−f_b)²]` to each of the **three** (base, apex) decompositions of a
triangle and sum the brackets:

```
(g_ab²+g_bc²+g_ca²)  ≤  2[(g_ac²+g_cb²) + (g_ba²+g_ac²) + (g_cb²+g_ba²)]
                      = 2 · 2(g_ab²+g_bc²+g_ca²).
```

So `T ≤ Σ_tri 4(g_ab²+g_bc²+g_ca²) = 4T`, i.e. **`T ≤ 4T`** — vacuous. The Jensen / link-averaging
version (TASK 3) `t_e g_e² ≤ 2 Σ_{c∈Link(e)}[g_ac²+g_cb²]` cancels the `t_e` factor but, summed over
edges, **regenerates the same RHS = 4T** (the warning's "each `g_ac²` is recounted `~t_ac` times" is
exactly right; the net constant is 4). Numerically `RHS/T = 4.000` on **all 13 graphs**.

> **There is no non-circular upper bound from link-averaging.** Re-expressing one triangle gap by
> the other two is circular by construction: the link expansion already *equals* `T`.

## TASK 2 (PRIORITY) — local triangle variance is global; no local bound exists

`Var(f_a,f_b,f_c)` (equivalently `(g_ab²+g_bc²+g_ca²)/9`) is **not** a function of `(d_a,d_b,d_c,λ)`.
Binning triangles by their degree-triple and measuring the spread of `Var_tri` *within* a bin:

| graph | #triangles | worst within-(equal degree-triple) `Var_tri` spread |
|---|---|---|
| K8  | 56  | ×374 (all triples `(7,7,7)`) |
| K15 | 455 | **×59904** (all triples `(14,14,14)`) |
| gnp30_0.3 | 140 | ×8005 |
| gnp30_0.6 | 845 | ×341 |

Triangles with **identical** local degrees have variances differing by up to **5 orders of
magnitude** — because the variance is set by the triangle's *global position* in the Fiedler field,
not by local degrees. The Fiedler equation is the reason: `Σ_{u~v}(f_u−f_v) = −λ f_v` constrains
only the **sum** of the `d_v` gradients at `v`; the three internal triangle gaps are an
uncontrolled subset. A candidate local bound `Var_tri ≤ λ²·meanf²/d_min²` has ratio ranging over
`[0, 47]` (dumbbell) — unbounded. **No local function of `(d_a,d_b,d_c,λ)` bounds `Var_tri`.**

### Why the corresponding direction-agnostic bound also fails to close

Dropping direction entirely (`(f_i−f_j)² ≤ 2(f_i²+f_j²)`) gives a *non-circular* but lossy local
bound `T ≤ 4 Σ_v τ_v f_v²` (`τ_v` = triangles through `v`), which closes **iff** `4τ_v ≤ λ d_v` at
every vertex. This fails everywhere, catastrophically on bottlenecks:

| graph | `λ₂` | aggregate `T/(λ·degQuad)` | crude `4Στf²/(λ·degQuad)` | `max_v 4τ_v/(λ d_v)` |
|---|---|---|---|---|
| K8 | 8.00 | 0.857 | 1.50 | 1.50 |
| gnp30_0.6 | 9.94 | 0.527 | 1.33 | 2.54 |
| deg2d40_0.6 | 1.97 | 0.621 | 4.56 | 18.5 |
| twin50_2 | 1.03 | 0.401 | 49.8 | 93.5 |
| **dumbbell15** | **0.118** | **0.104** | **218.6** | **219.5** |

The decisive pattern: the aggregate slack is **largest** (ratio smallest, 0.10) exactly where the
local overcount is **largest** (×219) — the **bottleneck** graphs. There `λ₂ → 0` while local
triangle density `τ_v` stays high, but the *true* `T` is tiny because the Fiedler is nearly
**constant on each dense cluster** (all triangle gaps ≈ 0). The local bound, blind to this
flatness, multiplies the high `τ_v` by `f_v²` and explodes. Local/direction-agnostic bounds are
worst precisely where they would need to be tightest — an inverse correlation that dooms the route.

## TASK 4 — Fisher normalizations: bounded, but no path back to the aggregate

`[Σ_e t_e g_e² / w_e] / (λ·‖f‖²)` for the three weights (representative rows):

| graph | `/(d_a+d_b)` | `/min(d)` | `/√(d_a d_b)` |
|---|---|---|---|
| K15 | 0.464 | 0.929 | 0.929 |
| dumbbell15 | 0.050 | 0.104 | 0.101 |
| gnp30_0.6 | 0.209 | 0.515 | 0.427 |
| twin50_2 | 0.024 | 0.240 | 0.077 |
| grid5x5 | 0.163 | 0.404 | 0.334 |

The `(d_a+d_b)`-normalized energy is bounded (`≤ ~0.47·λ` across the corpus), but **none of these
implies the aggregate**, because there is no valid mechanism to reinsert the per-edge weight:

```
T = Σ_e (t_e g_e²/w_e)·w_e  ≤  (max_e w_e)·Σ_e t_e g_e²/w_e          [loses, max w_e ~ 2Δ]
T  ≤  √(Σ t_e g_e²/w_e) · √(Σ t_e g_e²·w_e)   (Cauchy–Schwarz)       [2nd factor ≥ T]
```

Both go the wrong way: the only ways to recover `T` from a `1/w_e`-normalized sum re-introduce a
factor of order `Δ` (max degree) or an even-larger weighted sum. The normalization removes the
unbounded `t_e`-growth from the *display*, but not from the *inequality*. "Multiplying by
`degQuad`" has no closing identity: `degQuad = Σ_v d_v f_v²` does not telescope against
`Σ_e t_e g_e²/w_e`.

## Root cause — the Hadamard obstruction (consistent with prior findings)

`T = fᵀ L_t f` where `L_t = D_t − A_t` is the Laplacian of the **triangle-weighted** graph,
`A_t = A ∘ A²` (Hadamard product: `(A_t)_{ij} = A_{ij}·(A²)_{ij} = t_{ij}` on edges). The aggregate
asks `fᵀ L_t f ≤ 2λ fᵀ D f` for the Fiedler `f`. The truth of this rests on **eigenvector
localization** — `f` is flat where `A∘A²` is heavy (dense, high-triangle regions) — which is a
global spectral property of the Hadamard product `A∘A²`. Hadamard products do not interlace or
commute with the spectral decomposition, so any **local** surrogate (triangle inequality,
per-triangle variance, per-vertex degree bound, per-edge Fisher normalization) is **direction-** or
**position-agnostic** and cannot see the flatness. This is exactly the obstruction recorded for the
other entropy/distance attempts.

## TASK 5 — Report

| question | answer |
|---|---|
| **(a)** valid *non-circular* upper bound from link-averaging? | **No.** Link-averaging is an identity-in-disguise: `T ≤ 4T` (factor `= 4.000` on all 13 graphs). |
| **(b)** bound sharp enough to close the aggregate? | **No.** The only *non-circular* local bound (`T ≤ 4Στ_v f_v²`) overcounts by ×1.5 (cliques) to **×219** (bottlenecks); it would need `4τ_v ≤ λ d_v`, which is false everywhere. |
| **(c)** a Lean-formalizable *local* inequality? | **No useful one.** The local pieces (triangle inequality; `(f_i−f_j)² ≤ 2(f_i²+f_j²)`; `Σ_{u~v}(f_u−f_v)=−λf_v`) are each formalizable, but as closing bounds they are either **circular** (triangle inequality) or **false** (`4τ_v ≤ λ d_v`). `Var_tri` has no local functional bound (spread ×60000 within a degree class). |

**Conclusion.** Triangle links do **not** impose enough local rigidity on Fiedler gradients to bound
`T`. The inequality is genuinely **global/spectral**: its slack is concentrated exactly on the
bottleneck graphs where local triangle density is high but `λ₂` is small, and there the smallness of
`T` is due to Fiedler flatness on dense clusters — invisible to every local/Fisher surrogate tested.
The log-Sobolev / Fisher framing reduces to the same `A∘A²` Hadamard spectrum that the matrix and
entropy routes already hit. No new Lean-formalizable path emerges; `aggregate_triangle_poincare`
remains open, and a closing argument must be global (eigenvector localization on `A∘A²`), not local.
