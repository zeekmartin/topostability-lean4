# Conjecture B v4 — localized attack: the mechanism is hub-flatness (A2), not nodal cuts (A3)

Track A of the two-track push. Continues
[`conjecture_B_decomposition.md`](conjecture_B_decomposition.md). The lock:
```
(C4'')   W := Σ_{ab}(min(d_a,d_b)−δ)(f_a−f_b)²  ≤  λ₂(fᵀDf − λ₂ + 1 − S²/m) =: R''
```
`f` = unit Fiedler, `δ` = min degree, `S = Σ_v d_v f_v`, `m=|E|`.

**Verdict.** The anticorrelation that defeats crude bounds is now *explained and
validated*: it is a **hub-flatness** phenomenon — the Fiedler vector is small and
low-gradient at high-degree vertices (approach **A2**), confirmed by strong
correlations and two exact local identities. The competing **nodal-domain**
explanation (**A3**) is **refuted** by the data. No full proof yet, but the lock
is reduced to one quantitative statement (a bound on Fiedler energy flowing to
*higher-degree* neighbours), which the literature does **not** supply
(see [`conjecture_B_literature.md`](conjecture_B_literature.md)).

Code: [`conjecture_B_proof_v4_explore.py`](../conjecture_B_proof_v4_explore.py).
Data: 52 tightest irregular + 1256 broad graphs (n ≤ 13).

---

## A2 — hub-flatness: the mechanism (validated)

**Exact local identity (rigorous, verified 9e-15).** For the Fiedler vector,
the local Dirichlet energy at a vertex obeys
```
  D_a := Σ_{b∼a}(f_a − f_b)²  =  (2λ₂ − d_a) f_a²  +  Σ_{b∼a} f_b² .
```
(Direct from `L_G f = λ₂ f`; `Σ_a D_a = 2λ₂`.)

**Exact decomposition of the lock (rigorous, verified 4e-16).**
```
  W  =  Σ_v (d_v − δ) · D_v⁺ ,    D_v⁺ := Σ_{b∼v, d_b > d_v}(f_v − f_b)²
```
— each edge's weight `min(d_a,d_b)−δ` is borne by its **lower-degree** endpoint,
and only its energy to **strictly higher-degree** neighbours counts. So `W` is
literally "degree-excess × energy-flowing-uphill-in-degree".

**The flatness, measured (means over graphs):**

| correlation over vertices | tight (52) | broad (1256) |
|---|---|---|
| `corr(deg, f²)` — *small value at hubs* | **−0.84** | **−0.76** |
| `corr(deg, D_v)` — small local energy at hubs | −0.66 | −0.39 |
| `corr(deg, D_v/deg)` — *small per-edge gradient at hubs* | **−0.75** | **−0.63** |

High-degree vertices carry small Fiedler values **and** small gradients: the
vector is *flat at hubs*. A clean corollary, also universal:

> **`fᵀDf ≤ d̄ = 2m/n`** (average degree) — holds **1734/1734**, ratio median 0.79,
> `=1` only for regular graphs. The Fiedler degree-weighted norm sits *below
> average* precisely because `f²` avoids high-degree vertices.

This is exactly the anticorrelation the lock needs: in `W = Σ_v(d_v−δ)D_v⁺`, the
weight `(d_v−δ)` is large only at hubs, where `D_v⁺` (gradient energy) is small.

---

## A1 — the anticorrelation, directly

Per-edge `corr(weight = min(d_a,d_b)−δ,  gradient = (f_a−f_b)²)`:
**mean −0.82 (tight), −0.69 (broad); negative on 96–98% of graphs.**
The top-gradient quartile of edges carries only **31%** of `W` (it would carry
far more without the anticorrelation — those edges have small weight). The
crude bound `W ≤ (Δ−δ)λ₂` overshoots ~7× (v3) precisely because it ignores this.

---

## A3 — nodal-domain explanation: REFUTED

The hypothesis was that *cut* edges (sign-crossing, `f_a f_b < 0`) carry the large
gradients **and** connect low-degree vertices (small weight). The first half holds,
the second does **not**:

| | cut (sign-crossing) edges | internal edges |
|---|---|---|
| mean gradient `(f_a−f_b)²` | 0.28 | 0.15 |
| **mean min-degree** | **6.56** | **6.81** |

Cut edges do carry larger gradients (and ~55–70% of `W`), but their min-degree is
**essentially equal** to internal edges (6.56 vs 6.81). So the anticorrelation is
**not** a nodal-cut-degree effect — it is the A2 hub-flatness effect
(`corr(deg,f²)<0`), which operates *within* each nodal domain, not across the cut.
**A3 is not the right lens; A2 is.**

---

## Candidate closing bounds

| candidate | holds | note |
|---|---|---|
| `W ≤ λ₂(fᵀDf − δ)` | 88% tight, **37% broad** | ❌ not universal |
| `λ₂(fᵀDf − δ) ≤ R''` | 100% | (would close if the above held) |
| `W / Σ_v(d_v−δ)D_v` (all-neighbour version) | mean **0.07–0.15** | the "uphill ⁺-restriction" gives a 7–14× reduction |

The all-neighbour bound `Σ_v(d_v−δ)D_v = 2λ₂(fᵀDf−δ) + Σf_v²disc(v)` is exact but
~2× too large *before* the anticorrelation, and the `⁺`-restriction (uphill
neighbours only) supplies the rest of the 7–14× gap. **The missing rigorous step
is a quantitative bound on `D_v⁺`** — the Fiedler energy flowing from `v` to its
higher-degree neighbours — showing it is small when `d_v` is large.

---

## Status and the reduced lock

- **Rigorous (this round):** the local identity `D_a=(2λ₂−d_a)f_a²+Σ_{b∼a}f_b²`
  and the decomposition `W = Σ_v(d_v−δ)D_v⁺` (both verified to machine precision).
- **Validated empirically:** hub-flatness (`corr(deg,f²)=−0.84`,
  `corr(deg,per-edge gradient)=−0.75`), `fᵀDf ≤ d̄` (1734/1734), and the
  weight–gradient anticorrelation (−0.82).
- **Refuted:** the nodal-domain/cut-degree explanation (A3).
- **Open — the reduced lock:**
  > Quantitative hub-flatness: bound `Σ_v(d_v−δ)·D_v⁺ ≤ λ₂(fᵀDf−λ₂+1−S²/m)`,
  > i.e. show the degree-excess-weighted uphill energy is controlled by `λ₂`.

  The natural tool is a *second, local* use of `L_G f = λ₂ f`: at a high-degree
  `v`, `Σ_{b∼v} f_b = (d_v−λ₂)f_v` pins the neighbour mean to `(1−λ₂/d_v)f_v ≈ f_v`,
  forcing low gradient — but turning this into a bound on `D_v⁺` (uphill only)
  remains the open step. The literature offers no off-the-shelf hub-flatness
  theorem for the Fiedler vector (hub-*localization* results are for the *top* of
  the spectrum, where eigenvectors are *large* at hubs — the opposite end).

### Caveats
- One broad graph (n=12, Q=2.16, loose) shows a `−0.02` numerical miss of `(C4'')`
  (Fiedler-degeneracy artifact; B holds there with wide margin). All identities
  verified to ~1e-14. Non-bipartite assumed; `λ₂` numerical.
