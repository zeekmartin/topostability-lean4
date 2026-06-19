# Conjecture B — the edge-variance form `T ≤ λ₂·G` (Scenario 2)

Per edge `e = {a,b}`: lift `h_e = f_a + f_b`, gradient `g_e = f_a − f_b`, `t_e = #common nbrs`.
`Σ_e g_e² = fᵀLf = λ₂`, `Σ_e h_e² = fᵀQf = 2fᵀDf − λ₂`, `S = Σ_e h_e = Σ_v d_v f_v`,
`T = Σ_e t_e g_e²` (triangle energy), `G := Σ_e h_e² − S²/m = Σ_e(h_e − h̄)² = m·Var_E(h)` (`h̄=S/m`).
Code: [`conjecture_B_edge_variance.py`](../conjecture_B_edge_variance.py), 580 graphs.

## ⚠️ Factor correction

From the determinant round, `det(M_low) = (4λ₂/n)(λ₂·G_det − m·T)` with `G_det = m·fᵀQf − S² = m·G`.
So `B ⟺ λ₂·G_det ≥ m·T ⟺ λ₂·m·G ≥ m·T ⟺`

> **`B ⟺ T ≤ λ₂·G`**   (no extra `m` on `T`).

The stated `mT ≤ λ₂G` is **off by a factor `m`** (it conflates `G` with `G_det = m·G`). Verified:

| inequality | holds |
|---|---|
| `T ≤ λ₂·G` (correct) | **`580/580`**, `T/(λ₂G)` max `0.829` |
| `m·T ≤ λ₂·G` (as stated) | `8/580` |

This resolves TASK 5's "something's wrong" (see the regular case below).

## TASK 1 — per-edge `t_e g_e²` vs `(h_e − h̄)²`

`B` reads `Σ_e t_e g_e² ≤ λ₂ Σ_e (h_e − h̄)²`. The per-edge version **fails**:

| test | value |
|---|---|
| `corr(t_e g_e², (h_e − h̄)²)` | `+0.31` (weak) |
| per-edge `t_e g_e² ≤ λ₂(h_e − h̄)²` | `81.4%` of edges (fails 19%) |
| universal `C` with `t_e g_e² ≤ C(h_e − h̄)²` | needs `C ≥ 2·10⁹` (vs `λ₂ ≈ 1.9`) — **dead** |

The LHS lives on the gradient `g²`, the RHS on the centered lift `(h−h̄)²`; they are different
edge functions (`g_e = h_e − 2f_b`), so no per-edge bound exists. The conjecture is genuinely
aggregate.

## TASK 2 — weighted vs unweighted; sufficient conditions

`T/λ₂ = (Σ t_e g_e²)/(Σ g_e²)` is the `g²`-weighted average of `t_e`. The **anti-correlation**
`corr(t_e, g_e²) = −0.46` (high-`t` edges carry low gradient — triangle hub-flatness) pulls this
average down. Sufficient conditions:

| condition | holds |
|---|---|
| `T ≤ λ₂²` (would suffice with `G ≥ λ₂`) | `444/580` (not always; `T ~ (Δ−1)λ₂`) |
| `T ≤ (Δ−1)λ₂` (rigorous, `t_e ≤ Δ−1`) | `580/580` |

So `T ≤ (Δ−1)λ₂` is a rigorous upper bound (from `t_e ≤ Δ−1`), but `(Δ−1)λ₂` can exceed `λ₂G` on
irregular graphs.

## TASK 3 — the variance `G ≥ λ₂`

> `G/λ₂`: min `1.066`, median `1.69` — **`G ≥ λ₂` on `580/580`.**

(`G = 2fᵀDf − λ₂ − S²/m`; rigorously `≥ λ₂` would need `2fᵀDf − S²/m ≥ 2λ₂`.) Combined with
`T ≤ λ₂²` this would close `T ≤ λ₂² ≤ λ₂·G`, but `T ≤ λ₂²` holds only `444/580` — so this clean
two-step path covers most but not all graphs.

## TASK 4 — Cauchy–Schwarz / clean sufficient condition

The clean sufficient `T ≤ (max_e t_e)·λ₂ ≤ λ₂·G` needs `G ≥ max_e t_e`, which holds on `168/580`
(29%) — works on dense/regular graphs, fails where `G` is small (bottlenecks). No edge-pair
Cauchy–Schwarz couples `T` (a `g²`-energy) to `G` (a centered-`h²` energy) in general; the two
energies live on orthogonal combinations of `f_a, f_b`.

## TASK 5 — regular graphs: a clean complete proof ✓

For a **`d`-regular** graph: `S = Σ_v d_v f_v = d·Σf_v = 0` (`f ⊥ 1`), so

> `G = Σ_e h_e² = fᵀQf = 2d − λ₂`,  and  `T = Σ_e t_e g_e² ≤ (d−1)·Σ_e g_e² = (d−1)·λ₂`

(using `t_e ≤ d−1`, `triCount_le_min_degree_sub_one`). Then

> `(d−1)·λ₂ ≤ (2d − λ₂)·λ₂ = λ₂·G  ⟺  2d − λ₂ ≥ d − 1  ⟺  λ₂ ≤ d + 1`,

which holds **always** for `d`-regular graphs by Fiedler's bound `λ₂ ≤ (n/(n−1))·δ = (n/(n−1))d ≤
d + 1` (last step `⟺ d ≤ n−1`). Therefore

> **`T ≤ (d−1)λ₂ ≤ λ₂·G`, i.e. Conjecture B holds for every regular graph.** □

Verified (with `K₈` at equality — the complete graph is the tight case, `λ₂ = d+1 = n`):

| graph | `d` | `λ₂` | `G = 2d−λ₂` | `T` | `(d−1)λ₂` | `λ₂G` | B |
|---|---|---|---|---|---|---|---|
| C₂₀ | 2 | 0.098 | 3.90 | 0 | 0.098 | 0.38 | ✓ |
| K₈ | 7 | 8.000 | 6.00 | 48.0 | 48.0 | 48.0 | ✓ (=) |
| Petersen | 3 | 2.000 | 4.00 | 0 | 4.00 | 8.00 | ✓ |
| Q₄ | 4 | 2.000 | 6.00 | 0 | 6.00 | 12.0 | ✓ |
| circ(13,{1,5}) | 4 | 2.623 | 5.38 | 0 | 7.87 | 14.1 | ✓ |
| K₃,₃ | 3 | 3.000 | 3.00 | 0 | 6.00 | 9.00 | ✓ |

## Conclusion

- **Corrected form:** `B ⟺ T ≤ λ₂·G`, `G = m·Var_E(f_a+f_b) = Σ(h_e − h̄)²` (the "mT" form was off
  by `m`; resolves the regular-case paradox).
- **Regular graphs are fully proved** by the clean chain `T ≤ (d−1)λ₂ ≤ λ₂·G` (using `t_e ≤ d−1`,
  `Σg² = λ₂`, `G = 2d−λ₂`, and `λ₂ ≤ d+1`), with equality at complete graphs.
- **Irregular graphs** remain open: the per-edge bound fails (TASK 1), `T ≤ λ₂²` covers only most
  graphs (TASK 2/3), and `G ≥ max t_e` only 29% (TASK 4). The obstruction is that `S ≠ 0` decouples
  `G = Σh² − S²/m` from the gradient energy `T` — the irregular coupling, as in every prior round.
  The next lever is a degree-discrepancy bound matching `T = Σt_e g_e²` to the *centered* edge-lift
  variance `G = Σ(h_e − h̄)²` (not the gradient `Σg²`), which is what the regular case sidesteps via
  `S = 0`.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `sum_sq_mul_card_sub_sq` — `(Σxᵢ²)·N − (Σxᵢ)² = ½Σ_{i,j}(xᵢ−xⱼ)²` (variance identity; corollary of
  `lagrange_identity` at `b≡1`). Specialised `x = h` gives `G_det = m·Σh² − S² = ½Σ_{e,e'}(h_e −
  h_{e'})²`, i.e. the manifestly-nonnegative `G = m·Var_E(h)`. (The regular-case proof uses the
  already-formalised `triCount_le_min_degree_sub_one` plus Fiedler `λ₂ ≤ δ`, classical; a full Lean
  regular-case theorem would need the edge-lift/`Q`/`G` framework as definitions.)
