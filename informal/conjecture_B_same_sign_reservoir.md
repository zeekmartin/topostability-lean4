# Conjecture B — the same-sign reservoir and per-domain localization

Continues [`conjecture_B_nodal_decomposition.md`](conjecture_B_nodal_decomposition.md). The
proved-in-Lean identity (`triEnergy_sub_two_lam_degQuad`) is

> `T − λ₂·fᵀDf = Δ + C_hard − C_same`,
> `Δ = Σ_v(τ_v − λ₂d_v)f_v²`, `C_hard = 2Σ_{cross} t_ab|f_af_b|`, `C_same = 2Σ_{same} t_ab f_af_b`,
> `τ_v = Σ_{u∼v} t_{vu}`.  Target: `Δ + C_hard ≤ C_same`.

Nodal domains `V+ = {f≥0}`, `V- = {f<0}`. Code:
[`conjecture_B_same_sign_reservoir.py`](../conjecture_B_same_sign_reservoir.py) (56 near-tight
families) cross-checked on the 560-graph corpus.

**Headline.** The full aggregate Poincaré is **asymptotically tight globally** (barbell ratio
→1) but this is an artefact of subtracting two huge near-equal clique energies. Splitting by
nodal domain dissolves it: the inequality localizes to a **symmetric single-signed-domain
statement** `C_same_d ≥ Δ_d + ½C_hard` (d∈{+,−}), which holds **560/560** and — in the binding
bottleneck regime where `C_hard = 0` — is a **domain-restricted aggregate Poincaré**
`T_d ≤ λ₂·Σ_{V_d} d_v f_v²` with **comfortable margin (ratio ≤ 0.76, never tight)**.

---

## TASK 1 — per-domain decomposition; where the fight is tightest

On every bottleneck family **`C_hard ≈ 0`**: the sign change sits on the bridge edge, which
carries no triangle. So the whole surplus is per-domain `Δ_d` vs `C_same_d`:

| family | `λ₂` | `Δ₊` | `C_same₊` | `C_hard` | `C_same/Δ` | `Q` |
|---|---|---|---|---|---|---|
| barbell(5,0)   | 0.298 | 5.39   | 5.88   | 0 | 1.092 | −0.99 |
| barbell(20,0)  | 0.091 | 170.1  | 170.9  | 0 | 1.005 | −1.59 |
| barbell(80,0)  | 0.024 | 3080.0 | 3081.0 | 0 | 1.000 | −1.88 |
| glue(40,40)    | 0.048 | 740.1  | 741.0  | 0 | 1.001 | −1.78 |
| K60−3 (dense)  | 58.0  | −31.0  | 25.8   | 51.7 | −0.59 | −62.0 |

Two regimes:
- **Bottleneck (barbell/lollipop/glue/chain-cliques):** `C_hard = 0`, `Δ_d > 0`, and
  `C_same_d/Δ_d → 1⁺` as the cliques grow — **the tight fight, and it is purely intra-domain.**
- **Dense (`K_n` minus a few edges):** `Δ_d < 0` (for `K_n`, `τ_v−λ₂d_v = −2(n−1) < 0`), so
  `C_same_d ≥ Δ_d` is slack by a mile and `C_hard` is harmlessly dominated.

The fight is tightest on **large balanced glued cliques** (barbell/glue), entirely inside each
nodal domain.

## TASK 2 — `C_same_+` vs `Σ_{V+} τ_v^same f_v²`: the claim is reversed

For same-sign edges `t_ab(f_a−f_b)² ≥ 0`, so by AM–GM **`C_same_+ ≤ Σ_{v∈V+} τ_v^{same} f_v²`** —
the opposite of the proposed `≥`. Verified `56/56` (and `560/560`); the gap is *exactly* the
same-sign-positive triangle energy:

> `Σ_{v∈V+} τ_v^{same} f_v² − C_same_+ = T_{++} := Σ_{ab∈E(V+)} t_ab(f_a−f_b)²`  (exact, 56/56).

So `C_same_+ = Σ_{v∈V+} τ_v^{same} f_v² − T_{++}`. Cauchy–Schwarz / AM–GM points the wrong way;
the useful content is this identity, not a bound.

## TASK 3 — eigen lower bound within a nodal domain (PROVED, unweighted)

For `v∈V+`, `Σ_{u∼v} f_u = (d_v−λ₂)f_v`; splitting neighbours by sign and using `f_u<0` for
`u∈V-`, `Σ_{u∈V+,u∼v} f_u = (d_v−λ₂)f_v − Σ_{u∈V-,u∼v} f_u ≥ (d_v−λ₂)f_v`. Multiply by `f_v>0`
and sum:

> **`2·Σ_{ab∈E(V+)} f_a f_b = Σ_{v∈V+} f_v Σ_{u∈V+,u∼v} f_u ≥ Σ_{v∈V+} (d_v−λ₂) f_v²`.**

Holds `560/560` (slack `≥ 0`, the boundary outflow `Σ_v f_v·|Σ_{u∈V-,u∼v}f_u| ≥ 0`). This is a
clean, fully-proved **unweighted** reservoir bound. The obstacle to closing the proof is that
the actual quantity is **triangle-weighted** (`t_{vu}`), and there is **no eigen-equation for the
triangle-weighted Laplacian** — the weighting cannot be passed through `Σ_{u∼v} t_{vu}f_u`.

## TASK 4 — triangle-Perron, per-domain inequality, and the localized reduction

- The "triangle-Perron" quantity is exactly the reservoir: `Σ_{v∈V+} f_v Σ_{u∈V+,u∼v} t_{vu} f_u
  = C_same_+` (identity, 56/56).
- **Per-domain `C_same_d ≥ Δ_d` holds `560/560`** (min ratio `1.0001`; asymptotically tight in
  *ratio* on big cliques, but the absolute surplus stays positive).

The decisive step is to write the per-domain surplus in closed form. From the identity,

> `Δ_+ − C_same_+ = T_{++} + Σ_{v∈V+}(τ_v^{cross} − λ₂ d_v) f_v²`,

so `C_same_+ ≥ Δ_+ ⟺` **`T_{++} + Σ_{v∈V+} τ_v^{cross} f_v² ≤ λ₂·Σ_{v∈V+} d_v f_v²`** — a
**domain-restricted aggregate Poincaré**. Crucially this is **not** asymptotically tight:

| inequality (both domains) | holds | max ratio (LHS/RHS) |
|---|---|---|
| `T_d ≤ λ₂·Σ_{V_d} d_v f_v²` (bare) | 560/560 | **0.738** |
| `T_d + Σ_{V_d} τ_v^{cross} f_v² ≤ λ₂·Σ_{V_d} d_v f_v²` (exact ⇔ `C_same_d≥Δ_d`) | 560/560 | **0.759** |

The global problem's tightness (ratio →1) was an artefact of comparing two `O(m³)` clique
energies; the **per-domain** inequality has a uniform `~24%` margin. **Localization removes the
asymptotic tightness.**

### Closing the `C_hard` term — the symmetric per-domain reduction

Per-domain `C_same_d ≥ Δ_d` alone yields only `T ≤ λ₂fᵀDf + C_hard` (summing the two domains
leaves an unabsorbed `C_hard`). The clean fix is to charge `C_hard` symmetrically:

> **Reduction.** `aggregate_triangle_poincaré ⟺` for **each** domain `d∈{+,−}`,
> `C_same_d ≥ Δ_d + ½·C_hard`,
> equivalently `T_d + Σ_{V_d}τ_v^{cross}f_v² + ½C_hard ≤ λ₂·Σ_{V_d} d_v f_v²`.

Summing the two halves gives exactly `C_same ≥ Δ + C_hard`, i.e. `Q ≤ 0`. **Verified `560/560`,
worst per-domain margin `+0.016` (never negative).** This is a genuine reduction of the open
`aggregate_triangle_poincare` to a **single-signed-domain** inequality, where every `f_v` has one
sign — the regime in which TASK 3's eigen bound and the apex identity have the most leverage.

## Status

- **Proved (Lean, `ConjectureB.lean`):** the master identity `triEnergy_sub_two_lam_degQuad`.
- **Empirical (560/560), open:** the per-domain reduction `C_same_d ≥ Δ_d + ½C_hard`, and its
  bottleneck specialization, the domain-restricted Poincaré `T_d ≤ λ₂·Σ_{V_d} d_v f_v²`
  (comfortable margin).
- **The remaining gap:** a *triangle-weighted* analogue of TASK 3's eigen bound. The unweighted
  reservoir bound is proved; passing the weights `t_{vu}` through is the missing lemma, since the
  triangle-weighted operator has no Fiedler eigen-equation.

**Next lever (open target):** prove the domain-restricted Poincaré `T_d ≤ λ₂·Σ_{V_d} d_v f_v²` on
a single-signed domain. This is the original aggregate Poincaré restricted to a sub-population on
which `f` does not change sign — strictly easier (margin ≤ 0.76 vs global ratio →1), and the right
object for the apex/eigen machinery. Avoids all closed routes (no per-edge, no per-apex Rayleigh,
no hub-flatness): the statement is itself an aggregate over the domain.
