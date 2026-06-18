# Conjecture B — the open-2-path energy vs. the R-diagonal

From [`conjecture_B_A2_triangle_gap.md`](conjecture_B_A2_triangle_gap.md): the exact identity
`T + Open = Σ_v[σ_v − (d_v−λ₂)²]f_v²` (`T = fᵀL_M f ≥ 0`, `Open = fᵀL_P f ≥ 0`,
`σ_v = Σ_{c∼v}d_c`) makes `aggregate_triangle_poincare` equivalent to

> **`Open ≥ Σ_v R_v f_v²`**,  `R_v = σ_v − (d_v−λ₂)² − λ₂ d_v = (σ_v − d_v²) + λ₂(d_v − λ₂)`.

This note analyses that diagonal-vs-open-energy inequality.
Code: [`conjecture_B_open2path_gap.py`](../conjecture_B_open2path_gap.py). 580 graphs (corpus +
barbell/glue/chain-clique). **Headline: the inequality is true (580/580) but it is *not*
localisable and the negative-`R` (high-degree hub) mass is essential** — in `83/580` graphs
`Open < Σ_v R_v^+ f_v²` yet `Open ≥ Σ_v R_v f_v²`. The hubs' negative `R` is exactly the global
sign information the proof must keep.

---

## TASK 1 — sign structure of R_v

Since `λ₂ ≤ δ ≤ d_v` (algebraic connectivity ≤ min degree), `d_v − λ₂ ≥ 0`, so the spectral term
`λ₂(d_v−λ₂) ≥ 0` always. The sign of `R_v` is governed by the **degree-assortativity** term
`σ_v − d_v² = Σ_{c∼v}(d_c − d_v)`:

| quantity | value |
|---|---|
| fraction of vertices with `R_v > 0` | min `0.59`, median **`0.81`**, max `1.00` |
| graphs with **all** `R_v > 0` | `34/580` (regular / near-regular) |
| `Σ_{R>0} R_v f_v²` (median) | `21.5` |
| `Σ_{R≤0} R_v f_v²` (median) | **`−0.33`** (negative reservoir) |
| `corr(R_v, d_v)` | **`−0.65`** |
| `corr(R_v, τ_v)` | `−0.62` |
| `corr(R_v, open-deg p_v)` | `+0.28` |
| `corr(R_v, f_v²)` | `+0.10` |

**`R_v < 0` on high-degree hubs.** `R_v` is strongly anti-correlated with degree and triangle
degree: a hub whose neighbours are lower-degree has `σ_v − d_v² < 0` large enough to overcome
`λ₂(d_v−λ₂)`. On regular graphs `σ_v = d_v²` so **every** `R_v = λ₂(d−λ₂) > 0`. The positive `R`
mass sits on the lower-degree, high-open-2-path vertices (`corr(R, p_v) > 0`).

Exact decomposition of the negative part (purely algebraic, no eigen; residual `3·10⁻¹³`):

> **`Σ_v (σ_v − d_v²) f_v² = − Σ_{ab∈E} (d_a − d_b)(f_a² − f_b²)`**,
> hence `Σ_v R_v f_v² = − Σ_{ab∈E}(d_a−d_b)(f_a²−f_b²) + λ₂(fᵀDf − λ₂)`.

The hub negativity is an **edge antisymmetry** `(d_a−d_b)(f_a²−f_b²)`: positive when degree and `f²`
are co-monotone across an edge.

## TASK 2 — localization of Open

`Open = ½ Σ_v Open_v`, `Open_v = Σ_b p_{vb}(f_v−f_b)²` (open-2-path energy incident to `v`), where
`p_{vb} = (A²)_{vb}` for non-adjacent `v,b`. Equivalently `Open = Σ_{induced P₃ \,a−c−b}(f_a−f_b)²`
(sum over cherries that are not triangles).

> Fraction of total `Σ_v Open_v` carried by `R_v > 0` vertices: **median `0.88`**, min `0.45`.

**Open is concentrated where `R_v > 0`** — encouraging, the open energy lives on the same
(low-degree, high-open-degree) vertices that carry the positive demand. But concentration is not
domination (see TASK 3/4).

## TASK 3 — candidate inequalities (all fail with the positive part `R⁺`)

| inequality | holds |
|---|---|
| **local** `½ Open_v ≥ R_v⁺ f_v²` (per vertex) | `15031/20767` vertices (**72.4%**) |
| agg over nodal `V+` | `344/580` |
| agg over nodal `V−` | `339/580` |
| agg over `{R_v>0}` | `218/580` |
| agg over high-degree half | `498/580` |
| agg over high-`|f|` half | `117/580` |
| agg over **ALL** (`½ΣOpen_v = Open ≥ Σ R⁺ f²`) | `497/580` |

**No natural set `S` closes it using `R⁺`.** The "ALL" row is the crucial one: `Open ≥ Σ_v R_v⁺ f_v²`
fails in `83/580` graphs — because it *drops* the negative-`R` hub mass. The true inequality
`Open ≥ Σ_v R_v f_v²` (with the negative terms) holds `580/580`.

## TASK 4 — spectral Rayleigh on `L_P`

| ratio | min | median | max |
|---|---|---|---|
| `Open / Σ_{R>0} R_v f_v²` (positive part only) | **`0.076`** | `1.09` | `2.37` |
| `Open / Σ_{ALL} R_v f_v²` (true, denom>0) | **`1.017`** | `1.31` | — |

The first ratio drops to `0.076`: the open energy can be far below the positive-`R` mass *taken
alone*. The second ratio (the genuine inequality, including the negative hub mass in the
denominator) is `≥ 1` on all `580` graphs — this **is** `Q ≤ 0`. So a spectral lower bound on
`L_P` restricted to the positive-`R` region **cannot** work: it would prove the false `R⁺` version.
The negative mass is not slack to be discarded; it is load-bearing.

## TASK 5 — exact identity search

Verified exact (machine zero):
- `Open − Σ_v R_v f_v² = λ₂fᵀDf − T = −Q` — i.e. this difference *is* the aggregate slack itself
  (**circular**: no new sign-exposing structure from this rearrangement).
- `Open = ½ Σ_v Open_v = Σ_{induced P₃}(f_a−f_b)²` (sum over unordered non-triangle cherries;
  a manifest sum of squares — this is just `fᵀL_P f` with `L_P` PSD).
- `Σ_v(σ_v−d_v²)f_v² = −Σ_{ab∈E}(d_a−d_b)(f_a²−f_b²)` (assortativity edge-sum; **formalised**).

No decomposition makes `Open − Σ R_v f_v²` manifestly nonnegative: it equals `−Q`, and the only
nonnegativity available (`Open ≥ 0`, `T ≥ 0`) is too weak. The obstruction is structural — the
negative hub terms must cancel against `Open` *globally*, not term-by-term.

## Conclusion

The inequality `Open ≥ Σ_v R_v f_v²` is true and clear of tight (ratio `≥ 1.017`), but:
- it is **not localisable** — `½Open_v ≥ R_v⁺ f_v²` fails at `28%` of vertices and no set `S` repairs it;
- the **negative-`R` hub mass is essential** (`83/580` graphs need it), so any "bound `Open` below the
  positive demand" strategy is provably dead;
- rearranging `Open − Σ R f²` is circular (it equals `−Q`).

This is the same lesson as the per-edge and per-apex routes, now sharpened: the proof must preserve
the **global sign information** carried by the high-degree hubs (`R_v < 0`), where `f²` is small
(hub-flatness) but the contribution is structurally required. The open energy must be matched
against the *full* signed `R`-diagonal at once.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `degAssort_edge_identity` — `Σ_{i,j}[i∼j](d_j−d_i)f_i² = −½ Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)`,
  the exact edge-antisymmetry form of the assortativity diagonal `Σ_v(σ_v−d_v²)f_v²` (the
  negative-`R` hub mass). Pure double-sum algebra, no spectral hypothesis.

**Next lever (open, not a closed route):** match `Open = fᵀL_P f` against the *signed* `R`-diagonal
globally — e.g. find a single PSD form `B ⪰ 0` with `fᵀBf = Open − Σ_v R_v f_v²` that uses the
edge-antisymmetry `(d_a−d_b)(f_a²−f_b²)` to absorb the hub terms, rather than bounding positive and
negative parts separately.
