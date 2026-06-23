# Conjecture B — the aggregate slack as an eigenspace-PSD quadratic form

Attack `Slack = 2λ·degQuad − T ≥ 0` as a global quadratic form (no `B2′`, no local/per-apex/CS bounds).
**Result: `Slack = 2·fᵀQf` with `Q = λD − L_t` (`L_t` = triangle Laplacian). `Q` is NOT globally PSD
(8/42) — it is wildly indefinite on dense irregular graphs (min eig `−5629`). BUT `Q ⪰ 0 restricted to
the `λ₂` eigenspace `E_{λ₂}` (42/42, margin `≥ 0.141`)** — so the aggregate holds for *every* Fiedler,
characterised by an eigenspace-restricted PSD condition (the "trace-route" flavour), not a global one.
Code: [`aggregate_triangle_slack_global.py`](../aggregate_triangle_slack_global.py).

## TASK 1 — slack as an exact quadratic form

`T_unord = Σ_e t_e g² = fᵀL_t f` where **`L_t = diag(rowsum(A²⊙A)) − (A²⊙A)`** is the triangle
Laplacian (`A²⊙A` = common-neighbour counts `t_e` on edges; verified `fᵀL_t f = T_unord`, err `5·10⁻¹²`).
With `degQuad = fᵀDf` and `T_ord = 2·T_unord`:

> **`Slack_ord = 2λ·degQuad − T_ord = 2·fᵀQf`, `Q = λD − L_t`.**

So `aggregate ⟺ fᵀQf ≥ 0` at the Fiedler (`Q ⪰ 0` on the relevant subspace).

## TASK 2 — `Q = λ₂D − L_t`: indefinite globally, PSD on `E_{λ₂}`

| where | `Q ⪰ 0` holds | min eigenvalue (corpus) |
|---|---|---|
| globally | 8/42 | **−5629** (deg2d80_0.95) |
| on `1⊥` | 9/42 | **−5623** |
| **on `E_{λ₂}` eigenspace** | **42/42** | **+0.141** |

> **`Q` is far from globally PSD** (dense irregular graphs make `λD − L_t` hugely indefinite: a
> high-degree vertex with few triangles has `L_t` tiny but the *other* rows dominate). **Yet on the
> `λ₂` eigenspace (incl. degenerate, mult up to 49 for `K₅₀`), `Q ⪰ 0` with a uniform margin `≥ 0.141`**
> — the aggregate holds for *all* Fiedlers, not just one.

This is the **eigenspace-restricted PSD** characterisation (analogous to the gap's `M_gap` trace route):
the slack form is positive *only after* restricting to `E_{λ₂}`; the eigenvector relation `Lf = λf` is
what makes `fᵀ(λD − L_t)f ≥ 0`.

## TASK 4 — minimum slack and eigenstructure of near-extremals

| graph | class | slack/RHS | min eig `Q` (global)/λ | mult |
|---|---|---|---|---|
| `K₅₀` | REGULAR | **0.0204** | +1.00 (PSD) | 49 |
| cocktail₆ | multipartite | 0.200 | +0.40 (PSD) | 6 |
| gnp(40,.7) | RANDOM | 0.307 | **−3.0** (indef) | 1 |
| deg2+dense(80,.95) | TYPE A | 0.342 | **−2816** (indef) | 1 |
| deg2+dense(60,.7) | TYPE A | 0.373 | −767 (indef) | 1 |

> **Minimum slack/RHS ≈ 0.02** (`K_n`, the regular extremal, PROVEN). The smallest *irregular* slack is
> ≈ 0.31 (well away from 0). Near-extremals split cleanly: `K_n`/multipartite have `Q` globally PSD
> (`min eig/λ ∈ {1, 0.4, 2}`); irregular graphs have `Q` globally indefinite (min eig `≪ 0`) but
> eigenspace-PSD. The extremizer (`K_n`) is the *most globally-PSD* and the *tightest* slack.

## TASK 3 — `K_n` decomposition

For `K_n`: `L_t = (n−2)L`, so `Q = λD − L_t = n(n−1)I − (n−2)L`, eigenvalues `n(n−1)` (on `1`) and
`n` (on `1⊥`). Fiedler slack `= fᵀQf = n` (`f ⊥ 1`), `RHS_half = λ·degQuad = n(n−1)`, so
**`slack/RHS = 1/(n−1)`** (matches the prompt). General `Slack = fᵀQf` decomposes as the `K_n` form
`n(n−1)I − (n−2)L` *plus* the missing-triangle correction `(n−2)L − L_t` (positive when triangles are
missing, i.e. sparse core) — which is exactly why sparse graphs have *more* slack (smaller `T`).

## Conclusion

- **`Slack = 2·fᵀ(λD − L_t)f`** (`L_t` triangle Laplacian) — exact quadratic form.
- **`Q = λ₂D − L_t` is NOT globally PSD** (indefinite, min eig `−5629` on dense irregular) — no global
  matrix proof. **But `Q ⪰ 0 on `E_{λ₂}`** (42/42, margin `≥ 0.141`) — aggregate holds for every
  Fiedler, an eigenspace-restricted PSD condition.
- **`K_n` is the extremal** (slack/RHS `= 1/(n−1) → 0`, globally PSD, PROVEN); irregular slack `≥ 0.31`.
- The open core is `Q ⪰ 0 on E_{λ₂}` — the same eigenspace/trace-route territory as the gap; the
  `Lf = λf` relation is essential (no global PSD, no local bound).

## Lean
No change. `aggregate_triangle_poincare` stays the direct sorry on `T ≤ 2λ·degQuad`. The cleanest matrix
characterisation is now explicit: `Slack = 2fᵀ(λD − L_t)f` with `L_t` the triangle Laplacian, and the
open content is `(λ₂D − L_t) ⪰ 0 on E_{λ₂}` (eigenspace-PSD, margin `≥ 0.14`) — the trace/eigenspace
route, not a global PSD or a local apex bound. Regular case proved (`aggregate_triangle_poincare_regular`).
