# Conjecture B — the `F = Σ_v(d_v−1)D_v` route is DEAD

Test the intermediate `F = Σ_v(d_v−1)D_v` (`D_v = Σ_{u∼v}(f_v−f_u)²`) between `B2′` and `2λ·degQuad`.
`B2′ ≤ F` is trivial (`min(d_a,d_b) ≤ d_v` per orientation). **Result: `F ≤ 2λ·d_eff` is FALSE —
holds only 15/48, fails 33/48 with overshoots up to ×14. The step `B2′ ≤ F` is catastrophically lossy
on exactly the bottleneck families (TYPE A, clique+star): it discards the degree-asymmetry energy
`Σ_e|d_a−d_b|g²`, which is huge there. The `min(d_a,d_b)` in `B2′` is ESSENTIAL.** Route DEAD. Code:
[`conjecture_B_F_test.py`](../conjecture_B_F_test.py).

## The exact algebra

`F = Σ_v(d_v−1)D_v = Σ_e(d_a+d_b−2)g² = W − 2λ` (`W = Σ_e(d_a+d_b)g²`). The cost of `B2′ ≤ F`:

> **`F − B2′_ord = Σ_e |d_a − d_b| · g_e²`** (degree-imbalance energy), since
> `(d_a+d_b) − 2·min(d_a,d_b) = |d_a−d_b|`. For regular graphs this is `0` (`F = B2′`); for irregular
> graphs it is the Fiedler-gradient-weighted degree imbalance — large exactly where the bottleneck
> concentrates the gradient.

## TASK 1/2 — `F > 2λ·d_eff` ⟹ ROUTE DEAD (33/48)

| graph | class | `F/(2λd_eff)` | `B2′/(2λd_eff)` | cost (imbal/RHS) |
|---|---|---|---|---|
| star15+15 | clique+star | **14.00** | 0.00 | 14.00 |
| deg2+dense(80,.9) | TYPE A | **12.62** | 0.68 | 11.94 |
| twin-port `K₈₀` d2 | TYPE A | **5.94** | 0.61 | 5.33 |
| gnp(60,.7) | RANDOM | **1.45** | 0.97 | 0.57 |
| `K₅₀` | REGULAR | 0.980 | 0.980 | 0.00 |

> **`F` overshoots `2λ·d_eff` by up to ×14.** Failures: TYPE A (21), clique+star (3), random dense (9).
> Only REGULAR (`F = B2′`, cost 0) and TYPE B (sparse, cost ≤ 0.32) survive.

## TASK 4 — cost of the step `B2′ ≤ F`, by class

| class | `B2′/(2λd_eff)` mean | `F/(2λd_eff)` mean | `F/(2λd_eff)` MAX | cost MAX |
|---|---|---|---|---|
| REGULAR (incl `K_n`) | 0.888 | 0.888 | 0.980 | **0.000** |
| TYPE B (lollipop/barbell) | 0.184 | 0.340 | 0.527 | 0.324 |
| RANDOM (dense) | 0.923 | 1.203 | 1.455 | 0.567 |
| **TYPE A** (deg2+dense, twin) | 0.699 | **5.092** | **12.62** | **11.94** |
| **clique+star** | 0.000 | **10.00** | **14.00** | **14.00** |

> The step costs **nothing** on regular (where `min = d`), but the imbalance energy `Σ|d_a−d_b|g²`
> EXPLODES on TYPE A / clique+star — there a low-degree port (`d = 2`) sits next to a high-degree clique
> (`d ≈ N`), `|d_a−d_b| ≈ N`, and the Fiedler gradient `g²` is concentrated on exactly those bottleneck
> edges. So `F` inflates by `O(N)` while `B2′` (using `min = 2`) stays bounded.

## Conclusion

- **The `F` route is DEAD** (`F ≤ 2λ·d_eff` fails 33/48, ×14 overshoot). `F` is the per-orientation
  degree energy; replacing `min(d_a,d_b)` by `d_v` discards `Σ_e|d_a−d_b|g²`, which is unbounded on
  bottleneck families.
- **The `min(d_a,d_b)` in `B2′` is essential** — any degree relaxation that loses the min (`F`, or the
  constant-`α` `W`-route from the previous round) dies on TYPE A / clique+star.
- **This sharpens the proof direction for `B2prime_le_two_lam_degQuad`:** the proof must keep the
  degree-asymmetry (`min`), and (per `conjecture_B_B2prime_leaf_analysis.md`) interpolate from the
  regular case `min = d` where `F = B2′` and the bound is proven. The defect to control is precisely
  `Σ_e|d_a−d_b|g²` — but bounded *together with* the min, not added on top.

## Lean
No change. `B2prime_le_two_lam_degQuad` stays the open leaf; `F` is ruled out as an intermediate. The
regular leaf (`B2prime_le_two_lam_degQuad_regular`) remains the proven anchor, and `min(d_a,d_b)` must
be retained in any future proof (the `F`/`W` degree relaxations are dead).
