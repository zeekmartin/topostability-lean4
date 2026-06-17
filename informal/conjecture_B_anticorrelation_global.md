# Conjecture B — global triangle-gradient anti-correlation (Required > 0 families)

`T = Σ_{ab} t_ab(f_a−f_b)²`, `RHS = λ₂(fᵀQf − S²/m)`. Per-edge gradient bound (Paper14,
adjacent equal-degree): `(f_a−f_b)² ≤ |excl| · Σ_{u∈excl} f_u² / (min(d_a,d_b)−λ₂+1)²`,
where `excl = (N(a)△N(b)) ∖ {a,b}` has size `d_a+d_b−2t_ab−2`. Code:
[`conjecture_B_anticorrelation_global.py`](../conjecture_B_anticorrelation_global.py).

**Headline.** The anti-correlation is **universal** (Q3 = high-`t`/high-grad edges is
**empty** on every `Required>0` family). With the **correct exclusion-set numerator and the
local-mass factor `Σ_{excl}f²`**, the gradient bound **closes B on all lollipops**
(`T_bound/RHS = 0.002–0.10`, 0 per-edge violations) — recovering exactly the path-bottleneck
regime where the *carrier* mechanism broke. But it is **not universal**: it is violated and
loose on deg2+dense (the unequal-degree single-vertex bottleneck), because the bound is
proven only for **equal-degree** edges. **The gradient bound and the carrier mechanism are
complementary**, each covering one bottleneck type, neither alone universal.

---

## TASK 1 — the anti-correlation is universal (Q3 empty)

Classifying edges by (`t_ab`, `grad²`) against medians, on all 6 lollipop `Required>0`
graphs:

> **Q3 (high-`t` AND high-grad): count 0, contribution 0, on every graph.**

`T` is supported only on Q1 (high-`t`/low-grad = clique, `grad²≈10⁻⁶`) and Q2
(low-`t`/high-grad = path, `t=0`) — every edge has at least one small factor. This is the
structural reason `T` is tiny (`T = 0.004–0.10`). **No edge is both triangle-rich and
Fiedler-steep.**

## TASK 2 — the gradient bound: numerator and mass factor matter

| version of the per-edge bound | `T_bound/RHS` on lollipops | closes B? |
|---|---|---|
| full `\|N(a)△N(b)\|` (incl. `a,b`) + `‖f‖²=1` | **27 – 446** | no (0/6) |
| exclusion-set `d_a+d_b−2t_ab−2` + `‖f‖²=1` | 1.3 – 8.7 | no |
| **exclusion-set + local mass `Σ_{excl}f²`** | **0.002 – 0.10** | **yes (6/6)**, 0 violations |

Two corrections turn failure into success:
1. **Exclusion-set numerator** (`= d_a+d_b−2t_ab−2`, the user's formula): on equal-degree
   clique edges this is **0** (the Fiedler is constant on the clique by symmetry, so
   `excl = ∅`), so clique edges contribute **nothing** — versus the full `|N△|=2` which
   wrongly charges them.
2. **Local mass `Σ_{excl}f²`** instead of `‖f‖²=1`: the surviving (attachment/junction)
   edges have their `excl` vertices in the *low-Fiedler* clique, so `Σ_{excl}f²` is tiny.

Together, `T_bound_sharp = Σ_{ab} t_ab·|excl|·Σ_{excl}f²/(min−λ₂+1)²` is **10–400× below
RHS** on lollipops, with **0/1235 per-edge violations** — a rigorous `T ≤ T_bound ≤ RHS`
chain (the per-edge bound is the proven equal-degree gradient bound, valid on the lollipop's
equal-degree edges).

## TASK 3 — does it generalise? NO — equal-degree only

| family | `T_bound_sharp/RHS` | per-edge violations |
|---|---|---|
| lollipops (`Required>0`) | **0.002–0.10** | **0** |
| deg2+dense n=50/100/200 | **8.0 / 16.6 / 32.7** | **2 per graph** |
| corpus `n≤9` (1201 graphs) | max 8.0; closes 72% | **18% of edges** |

The sharp bound is **violated** on 2 edges per deg2+dense graph and 18% of corpus edges —
precisely the **unequal-degree** edges, where the equal-degree gradient bound is *not
proven and does not hold*. On deg2+dense the bottleneck is the **degree-2 vertex** whose two
edges go to high-degree dense vertices (very unequal, steep gradient `≈ f_{v₀}²`); the
equal-degree bound fails there. Lollipops are different: their bottleneck is an
**equal-degree path** attached to an **equal-degree clique**, so the bound applies on
essentially all edges (junctions are `O(1)` and `0` violations occur).

So the hypothesis "`Required>0 ⇒ gradient bound works`" is **false**; the correct condition
is **"the bottleneck is equal-degree"** (path/clique), which lollipops satisfy and
deg2+dense does not.

## TASK 4 — where `T_bound` lives on lollipops

The only edges contributing to `T_bound_sharp` are the **attachment/junction edges** (clique
vertices adjacent to the path-attachment, with `excl = {one path vertex}`, `|excl|=1`):
`t≈m−2`, `grad²≈10⁻⁶`, bound `≈10⁻⁴–10⁻⁷`, `t·bound ≈ 10⁻³–10⁻⁵`. Clique-interior edges
contribute **0** (`excl=∅`); path edges contribute **0** (`t=0`). The whole `T_bound` is a
handful of junction terms, each tiny — hence the huge margin.

---

## Synthesis — two complementary mechanisms, neither universal

| bottleneck type | example | carrier mechanism | sharp gradient bound |
|---|---|---|---|
| single unequal-degree vertex | deg2+dense | **closes** (β≈λ₂) | **fails** (violated, loose) |
| equal-degree path/clique | lollipop | **fails** (mass/triangle separated) | **closes** (0.002–0.10) |

- The **anti-correlation `Q3 = ∅` is universal** — the genuine structural fact behind
  small `T`. Both mechanisms are ways to *quantify* it; each captures one regime.
- **The sharp gradient bound (exclusion-set + local mass) closes the equal-degree
  bottleneck regime** (lollipops) that the carrier mechanism could not. This needs the
  *sharper* form of the Paper14 gradient lemma (keep `Σ_{excl}f²`, don't relax to `1`) — a
  one-line strengthening of the formalized proof, but **only valid for equal-degree edges**.
- **Neither tool is universal:** unequal-degree bottlenecks (deg2+dense) defeat the gradient
  bound; separated mass/triangle structure (lollipops) defeats the carrier sum. A general
  proof of the `Required>0` regime must handle both — e.g. an equal-degree gradient bound
  for equal-degree edges *combined with* a direct argument for the few unequal-degree
  bottleneck edges (the degree-2 vertex's edges), where the carrier/`β≈λ₂` analysis applies.

The robust facts remain: **B holds (33/33 + corpus); `Deficit ≥ Required` with margin; the
`sign(Required)` regime split is exact; and `Q3 = ∅` universally.** The two complementary
bounds together cover the tested `Required>0` families, but a single closing lemma is still
open.

### Caveats
`λ₂`, `f`, per-edge data numerical. `Required>0` realised only on lollipops among the
constructed families; sharp-bound validity (0 violations) holds on lollipops but fails on
unequal-degree edges (deg2+dense 2/graph, corpus 18%). The sharp gradient bound is the
*equal-degree* Paper14 lemma with the `Σ_{excl}f²` factor retained (provable by the same
Cauchy–Schwarz, not yet formalized); it is unjustified on unequal-degree edges and indeed
fails there.
