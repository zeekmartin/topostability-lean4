# Conjecture B — positive/negative apex-surplus decomposition

`surplus_c = λ₂·mass_c − energy_c`, `mass_c = Σ_{v∈N(c)} f_v²`, `energy_c = E_{G[N(c)]}(f)`.
`Deficit = Σ_c surplus_c = λ₂fᵀDf − T`; `Required = λ₂(λ₂+S²/m−fᵀDf)`; `B ⟺ Deficit ≥
Required`. (`Σ_c mass_c = fᵀDf`, `Σ_c energy_c = T` — the apex identity, formalized in
`Paper15.lean`.) Code: [`conjecture_B_apex_surplus.py`](../conjecture_B_apex_surplus.py).

**Headline.** On deg2+dense the **entire `Deficit ≈ 2.0` is carried by exactly 2 apices** —
the **two neighbours of the degree-2 bottleneck vertex** — each with `surplus ≈ 1.0`. All
other apices net ≈ 0. Each carrier satisfies `ε := 1 − energy_c/(λ₂·mass_c) = 0.500`
*exactly* at every `n`, i.e. `energy_c = ½·λ₂·mass_c` and `surplus_c = ½·λ₂·mass_c`. The
mechanism uses the **eigen-equation** (the bottleneck forces `λ₂ ≈ d_{v₀} = 2`) plus
**hub-flatness** (`f ≈ 0` off the bottleneck) — **not `λ₂`-minimality.**

*(Note: an indexing slip in the first run probed the wrong vertex; `deg2dense` appends the
degree-2 vertex last. The order-independent sums below are correct; the per-vertex probe
was redone with the concentration vertex `= argmax f²`.)*

---

## TASK 1 — surplus by degree quartile (deg2+dense)

`Deficit ≈ 2.0`, total positive surplus ≈ 2.3, total negative ≈ 0.29, at all `n`. By degree
quartile the surplus appears as **~1.0 chunks in *varying* quartiles** (Q2+Q3 at n=50,
Q1+Q4 at n=100, Q1 at n=200, Q2+Q4 at n=500, Q3+Q4 at n=1000). This is the signature of
**two point carriers** whose degree (`≈ qn`, near the median) lands in different quartiles
across samples — *not* a degree-monotone surplus.

## TASK 2 — can low-degree apices close B? **No (and the premise is wrong).**

`low_surplus(d_c ≤ median)` vs `Required`: holds on n=50,200 but **fails on n=100,500,1000**
(flip-flops). Reason: the two carriers are **dense** vertices (degree `≈ qn`, right at the
median), so whether they fall in `d_c ≤ median` is essentially a coin flip — `low_surplus`
jumps between ≈1.0 (one carrier) and ≈2.0 (both). **The surplus is not carried by
low-degree apices**; the earlier "low-degree-half" reading was a median-split artifact.

## TASK 3 — closing-threshold by Good-set definition

deg2+dense, n=500, `Required = 1.25`, `Deficit = 1.99`:

| Good-set | needs | closes? |
|---|---|---|
| (a) `d_c ≤ k` | `k = max` (all apices) | only at q=1.0 — useless (carriers are mid-degree) |
| (b) `density(G[N(c)]) ≤ ρ` | `ρ ≥ 0.7` (≈ all) | useless (all neighbourhoods have density ≈ q) |
| **(c) `f_c² ≤ thr`** | **even `thr = q0.5`** | **closes (Σ_Good ≈ 1.7–1.98)** |

**The clean separator is `f_c²` (the apex's own Fiedler value), not degree or density.** The
carriers have `f_c² ≈ 0` (they are dense, low-Fiedler vertices), so `{c : f_c² small}`
captures them and excludes only the one high-`f` concentration vertex. The surplus comes
from the carriers' large *neighbourhood* mass, not their own value.

## TASK 4 — WHY: the bottleneck vertex and its two neighbours

Corrected probe (`conc = argmax f²`):

| `n` | conc degree | `f_conc²` | surplus on `N(conc)` | Deficit on all-other |
|---|---|---|---|---|
| 200 | 2 | 0.9949 | **1.991** | 0.023 |
| 500 | 2 | 0.9980 | **1.997** | −0.003 |
| 1000 | 2 | 0.9990 | **1.999** | 0.000 |

- The **degree-2 vertex `v₀` holds ~all the Fiedler mass** (`f_{v₀}² → 1`).
- Its **two neighbours `a,b` are the sole carriers**: `v₀ ∈ N(a), N(b)`, so `mass_a, mass_b
  ≈ f_{v₀}² ≈ 1`. The only Fiedler energy inside `G[N(a)]` is the edge `{v₀, b}`, giving
  `energy_a ≈ (f_{v₀}−f_b)² ≈ f_{v₀}² ≈ mass_a`. Hence `surplus_a = λ₂mass_a − energy_a ≈
  (λ₂−1)·f_{v₀}²`.
- **Every other (dense) apex has `mass_c ≈ 0`** (its neighbourhood avoids `v₀`, and `f ≈ 0`
  on the dense bulk), so `surplus_c ≈ 0`; the ~0.29 of negative surplus is spread in tiny
  amounts over dense apices where the local Poincaré slightly fails — negligible.

So `Deficit ≈ surplus_a + surplus_b ≈ 2(λ₂−1)f_{v₀}²`.

## TASK 5 — candidate lemma: `ε = ½` at the carriers (no minimality)

For both carriers, at **every** `n`:

> `mass_c ≈ energy_c ≈ f_{v₀}²`, and `ε_c := 1 − energy_c/(λ₂·mass_c) = 0.500` exactly,
> i.e. **`energy_c = ½·λ₂·mass_c`** and **`surplus_c = ½·λ₂·mass_c`**.

Why `ε = ½`: the degree-2 **bottleneck forces `λ₂ ≈ d_{v₀} = 2`** — from the eigen-equation
at `v₀`, `(d_{v₀} − λ₂)f_{v₀} = f_a + f_b`, and `f_a + f_b ≈ 0` (dense, hub-flat), so
`λ₂ → d_{v₀} = 2`. With `energy_c ≈ mass_c`, `ε = 1 − 1/λ₂ → ½`. **This uses only the
eigen-equation and hub-flatness — not minimality.**

Consequently `Deficit = Σ_{c∈N(v₀)} ½λ₂ mass_c ≈ ½λ₂·(2 f_{v₀}²) = λ₂ f_{v₀}²`, and B on
this family reduces to the concrete scalar inequality
`λ₂ f_{v₀}² ≥ Required = λ₂(λ₂ + S²/m − fᵀDf)`, i.e. `fᵀDf + f_{v₀}² ≥ λ₂ + S²/m` — which
holds with the ~50% margin measured in the deficit round.

**Candidate general lemma (the route to a proof):** the apex surplus localises at the
neighbours of *low-degree, high-Fiedler* vertices `v`, where `mass_c ≥ f_v²` (neighbourhood
contains `v`) and `energy_c ≤ (1 − (d_v−1)/d_v + o(1))·λ₂·mass_c` type bounds give
`surplus_c ≳ (λ₂ − 1)f_v²`. Summing over such `v` should produce `Deficit ≥ Required`
with a positive margin. The ingredients are the **eigen-equation** (`λ₂` vs local degrees,
`f`-concentration at bottlenecks) and **hub-flatness** (`Paper14`) — the analysis gives no
indication that `λ₂`-minimality is required, consistent with the stable ~1.5× margin.

---

## Synthesis

- The `Deficit` is **not** diffuse: on deg2+dense it is **two point masses** at the
  neighbours of the bottleneck vertex, each `≈ ½λ₂·mass_c` with `mass_c ≈ f_{v₀}²`.
- The right structural label for "surplus-carrying" apices is **small own Fiedler value
  but large neighbourhood mass** (`f_c² ≈ 0`, `mass_c ≈ 1`) — i.e. neighbours of the
  Fiedler-concentration vertex — *not* low degree or low density.
- The per-apex relation `ε = ½` is exact and explained by the bottleneck (`λ₂ ≈ d_{v₀}`),
  via the **eigen-equation + hub-flatness only**. This strengthens the deficit-round
  conclusion: the Dirichlet route closes B on the binding family with a **structural,
  minimality-free** surplus.

### Caveats
`λ₂`, `f`, per-apex energies numerical. deg2+dense `q=0.65`, `n` to 1000 (TASK 1/2/4/5);
TASK 3 at n=500. The "2 carriers" picture is exact on this single-bottleneck family; a
general graph has one carrier-pair per low-degree/high-Fiedler vertex — generalising the
`ε ≈ 1 − 1/d_v` per-apex bound and summing is the concrete next step toward a proof.
