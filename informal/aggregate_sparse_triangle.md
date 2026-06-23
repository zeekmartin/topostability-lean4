# Conjecture B — sparse-triangle aggregate Poincaré (crude bounds are too lossy)

Try to prove `T ≤ 2λ·degQuad` for sparse-triangle graphs via crude bounds. **Result: the crude
`maxt ≤ degQuad` bound (TASK 1) covers essentially only the *regular* case (already proved); the
triangle-count threshold (TASK 3) covers nothing (the `max g² ≤ 4` bound is far too loose). The
"sparse ⟹ small T" intuition is true but NOT captured by `max`/`count` bounds — they ignore the
*weighting* of `g²`. A clean sorry-free lemma `aggregate_triangle_poincare_of_maxt` is added (covers
`max_e t_e ≤ degQuad`), generalizing the regular case, but the uncovered set is *most irregular graphs*,
not just TYPE A dense-core.** Code:
[`aggregate_typeA_scalar.py`](../aggregate_typeA_scalar.py) (+ inline test).

## TASK 1 — `Δ−1 ≤ degQuad` / `maxt ≤ degQuad`

`T = Σ_e t_e g² ≤ max_e t_e · Σ_e g² = maxt · 2λ`, so `T ≤ 2λ·degQuad` follows from `maxt ≤ degQuad`
(`maxt ≤ Δ−1`). Coverage:

| family | `maxt ≤ degQuad` | `Δ−1 ≤ degQuad` |
|---|---|---|
| regular `K_n` | 3/3 | 3/3 |
| regular `rr` | 3/3 | 3/3 |
| sparse gnp (q ≤ .15) | **1/4** | 0/4 |
| dense gnp | 1/4 | 0/4 |
| deg2+dense (all) | **0** | 0 |
| twin-port | 0/4 | 0/4 |
| lollipop | 0/2 | 0/2 |

> **`maxt ≤ degQuad` covers only regular + a couple gnp.** It FAILS on sparse-triangle irregular graphs
> too — because `degQuad` (Fiedler-weighted degree) is small when `f` localizes, while `maxt` (a *local*
> max common-neighbour count) can still be moderate. The crude `max` ignores that few edges carry it.

## TASK 2/3 — triangle-count threshold (TOO LOOSE)

`T ≤ 3·num_triangles · max_e g²`, `max g² ≤ 4` (since `max|f_v| ≤ 1`), so `T ≤ 12·num_tri`. The threshold
`num_tri ≤ λ·degQuad/6` ⟹ `T ≤ 2λ·degQuad`:

| family | threshold met |
|---|---|
| all families | **0** |

> **The threshold covers NOTHING.** `max g² ≤ 4` is achieved only if `f` is fully localized on one vertex;
> for spread-out Fiedlers `max g² ≪ 4`, so `T ≤ 12·num_tri` overshoots by orders of magnitude. The crude
> *count* bound discards the (tiny) actual `g²` weights.

## TASK 4 — the clean sorry-free lemma (`maxt ≤ degQuad`)

> **`aggregate_triangle_poincare_of_maxt` (no `sorry`, in Lean):** if `t_e ≤ mt` on every edge,
> `λ ≥ 0`, `‖f‖² = 1`, and `mt ≤ degQuad`, then `triEnergy ≤ 2λ·degQuad`. Proof:
> `triEnergy ≤ mt·(Dirichlet) = mt·2λ ≤ degQuad·2λ`.

This **generalizes** `aggregate_triangle_poincare_regular` (`mt = d−1 ≤ d = degQuad`) and is the cleanest
3-line aggregate lemma. It covers exactly `{ max_e t_e ≤ degQuad }` — regular and genuinely
low-triangle-overlap graphs.

## TASK 5 — coverage of the full split

| route | covers | status |
|---|---|---|
| `aggregate_…_regular` / `_of_maxt` | `maxt ≤ degQuad` (regular + low-overlap) | **proved** |
| TYPE A bridge (`triEnergy_le_of_partition` + scalar) | dense-core bottleneck (`maxt ≫ degQuad`) | conditional (scalar open) |
| TYPE B | path bottleneck | proved (`conjectureB_regime_two_typeB`) |

> **Uncovered = most irregular graphs with `maxt > degQuad`** — NOT just TYPE A dense-core. The premise
> "gap = TYPE A dense-core only" is **too optimistic**: sparse/medium irregular gnp (`maxt > degQuad`)
> also fall outside `maxt ≤ degQuad`. The genuine sparse-triangle smallness of `T` is real but the crude
> bounds can't see it; only the *weighted* `Σ_e t_e g²` (with the actual `g²` localization) is small,
> which is the eigenspace/block-flatness content (`aggregate_typeA_scalar.md`).

## Conclusion

- **`maxt ≤ degQuad` covers only regular + a few** (sorry-free `aggregate_triangle_poincare_of_maxt`
  added, generalizing the regular case).
- **Triangle-count threshold covers nothing** (`max g² ≤ 4` hopelessly loose).
- **The sparse-triangle intuition holds but isn't captured by crude max/count bounds** — they discard the
  `g²` weighting. The uncovered set is most irregular graphs, broader than TYPE A dense-core.
- The real content remains the *weighted* aggregate (eigenspace-PSD `λD − L_t ⪰ 0 on E_{λ₂}` /
  block-flatness), not a crude bound.

## Lean
Added `aggregate_triangle_poincare_of_maxt` (sorry-free, covers `maxt ≤ degQuad`, generalizes
`_regular`). Did NOT touch `aggregate_triangle_poincare` or `conjectureB`. 3 sorrys unchanged
(`aggregate_triangle_poincare` 854, `typeA_slack_ge_required` 1034, `conjectureB` 1117).
