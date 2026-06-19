# Conjecture B — the weighted Bochner inequality from Γ₂ curvature (a decisive negative)

Target (`= −Q ≥ 0`, `Lf = λ₂f`, `f ⊥ 1`, `‖f‖ = 1`):

> **`2⟨d,Γ(f)⟩ ≤ Open + λ₂·fᵀDf + λ₂²`**,  `Γ(f)(v) = ½Σ_{u∼v}(f_v−f_u)²`,
> `Γ₂(f)(v) = ½(LΓ(f))(v) − λ₂Γ(f)(v)`.

Can a Bakry–Émery curvature bound (`CD(K,∞)`: `Γ₂ ≥ KΓ`) close it? Code:
[`conjecture_B_weighted_bochner.py`](../conjecture_B_weighted_bochner.py), 580 graphs, all residuals
machine-zero. **Verdict: no.** The degree-weighted `Γ₂` is a pure-`Γ` (Dirichlet) object that does
not contain the open-cherry energy `Open`, and the pointwise curvature constant is negative on every
graph.

---

## STEP 1 — explicit per-vertex Γ₂ (verified machine-precision)

From `Γ₂ = ½LΓ − λ₂Γ` and `L = D − A` (residuals `≤6·10⁻¹⁴`, 580 graphs):

> `Γ₂(f)(v) = (d_v/2 − λ₂)·Γ(f)(v) − ½·Σ_{u∼v}Γ(f)(u)`.

Unfolding the neighbour energies gives the **Jost–Liu-style triangle / 2-ball split**: with
`R(v) := Σ_{u∼v}Σ_{w∼u, w≠v}(f_u−f_w)²`,

> `Γ₂(f)(v) = ((d_v−1)/2 − λ₂)·Γ(f)(v) − ¼·R(v)`,  `R(v) = D_v + R_out(v)`,

where `D_v = Σ_{u,w∈N(v), u∼w}(f_u−f_w)²` is the **triangle (closed-cherry) energy** at `v` and
`R_out(v) = Σ_{u∼v}Σ_{w∼u, w∉N(v)∪{v}}(f_u−f_w)²` the **outgoing 2-ball** energy.

> **Key structural fact:** `Γ₂(v)` carries the *triangle* energy `D_v` (with a negative sign) and
> the *outgoing-edge* energy `R_out(v)`. The **open-cherry endpoint energy**
> `O_v = Σ_{y,z∈N(v), y≁z}(f_y−f_z)²` — whose sum is `Open` — **does not appear in `Γ₂(v)`.**

So `Γ₂` (a 2-ball *edge* energy) and `Open` (a neighbourhood *endpoint-pair* energy) are different
second-order objects. This is why per-vertex `Γ₂` correlates only `+0.19` with `O_v` (Bochner round).

## STEP 2 — exact identity for the degree-weighted Γ₂

(residual `3·10⁻¹¹`):

> **`⟨d,Γ₂(f)⟩ = ½·dᵀL Γ(f) − λ₂·⟨d,Γ(f)⟩ = ½·ℰ_L(d, Γ(f)) − λ₂·⟨d,Γ(f)⟩`**,

with `(Ld)_v = d_v² − σ_v` and `ℰ_L(d,Γ) = Σ_{ab∈E}(d_a−d_b)(Γ(f)(a)−Γ(f)(b))` the Dirichlet
pairing. **`⟨d,Γ₂⟩` is a pure-`Γ` (Dirichlet) functional — it contains no `Open` term.** Any
curvature bound `⟨d,Γ₂⟩ ≥ K⟨d,Γ⟩` therefore yields `½ℰ_L(d,Γ) ≥ (K+λ₂)⟨d,Γ⟩`, a statement about
`ℰ_L(d,Γ)`, *not* about `Open`. The degree-weighted `Γ₂` is structurally disconnected from the
target's open-energy side.

## STEP 3 — pointwise `CD(K,∞)` fails (K < 0 everywhere)

`K_pt := min_v Γ₂(f)(v)/Γ(f)(v)`:

| | value |
|---|---|
| `K_pt` (min / median / max) | `−3238` / `−144` / **`−1.76`** |
| graphs with `K_pt ≥ 0` (`CD(0,∞)`) | **`0/580`** |

`Γ₂(f)(v) ≥ K·Γ(f)(v)` holds only with **negative** `K` on every graph — these are bottlenecked
graphs (small `λ₂`), negatively curved at the bottleneck. No positive Ricci bound exists, so the
Lichnerowicz route (`λ₂ ≥ K`) is vacuous here.

## STEP 4 — integrated / degree-weighted `CD` also fails to reach the target

`K_int := ⟨d,Γ₂⟩/⟨d,Γ⟩`: min `−46.7`, median `−1.48`, max `2.57`; `≥0` on only `46/580`.

The target slack `−Q` is *strongly* anti-correlated with the `Γ₂` aggregates
(`corr(−Q,⟨d,Γ₂⟩)=−0.92`, `corr(−Q,Σ_vΓ₂)=−0.96`) — but this is a **scale artifact**: both `−Q`
and `⟨d,Γ₂⟩` track `⟨d,Γ⟩` in magnitude (with opposite sign), so they anti-correlate across graph
sizes. There is **no exact `Open`-free identity** linking `−Q` to `Γ₂` (STEP 2 shows `⟨d,Γ₂⟩` has no
`Open`). A curvature bound cannot manufacture the open energy.

## STEP 5 — Jost–Liu / Ollivier: a different curvature, still no `Open`

Jost–Liu's curvature bounds are for the **Ollivier–Ricci** curvature `κ(u,v)`, which on an edge `uv`
uses the **triangle count** `t_uv = |N(u)∩N(v)|` (common neighbours) and the degrees — *not* the
open-cherry endpoint energy. Triangle energy and open energy do correlate (`corr(T,Open)=+0.78`),
but neither the Bakry `Γ₂` nor the Ollivier `κ` produces `Open = Σ_v O_v`. Both curvatures see the
*triangle* (clustering) side; `Open` is the *complementary* (non-triangle) endpoint energy.

## Conclusion

**The Γ₂ / Bochner curvature route does not close the weighted inequality**, for a structural reason:

- `⟨d,Γ₂⟩ = ½ℰ_L(d,Γ) − λ₂⟨d,Γ⟩` is a **pure-`Γ` Dirichlet object with no `Open` term** (STEP 2);
- pointwise `CD(K,∞)` has `K < 0` on all 580 graphs (STEP 3); integrated `CD` bounds `ℰ_L(d,Γ)`,
  not `Open` (STEP 4);
- both graph curvatures (`Γ₂`, Ollivier) live on the **triangle/clustering** side, while the target
  needs the complementary **open-cherry endpoint energy** `Open` (STEP 1, STEP 5).

The target `2⟨d,Γ(f)⟩ ≤ Open + λ₂fᵀDf + λ₂²` genuinely requires coupling the degree-weighted carré
du champ to the *open* (non-adjacent neighbour-pair) energy. Curvature controls the adjacent
(triangle) structure and the Dirichlet energy of `Γ`, but it is blind to the open-endpoint energy.
A proof must use the **`A²` / 2-path operator** (which sees endpoint pairs at distance 2), not the
Bochner `Γ₂` (which sees 2-ball edge energies) — confirming the open-2-path operator route
(`conjecture_B_A2_triangle_gap.md`) over the curvature route.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `lapMatrix_mulVec_sum_zero` — `Σ_v (L g)_v = 0` (zero column-sum of the Laplacian; antisymmetry of
  the Dirichlet form). With the carré-du-champ identity (`lapMatrix_mulVec_sq`) this gives the
  integrated Bochner identity `Σ_v Γ₂(f)(v) = −λ₂·Σ_v Γ(f)(v) = −λ₂²`.

(STEP 1 and STEP 2 are exact but are immediate from the definition `Γ₂ = ½LΓ − λ₂Γ` together with the
already-formalised carré-du-champ product rule `lapMatrix_mulVec_sq`; no separate lemma added.)
