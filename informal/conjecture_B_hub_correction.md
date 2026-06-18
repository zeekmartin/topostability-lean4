# Conjecture B — the signed hub-correction term

From [`conjecture_B_open2path_gap.md`](conjecture_B_open2path_gap.md): `aggregate_triangle_poincare`
⟺ `Open ≥ Σ_v R_v f_v²`, and the negative-`R` (high-degree hub) mass is load-bearing. This note
isolates that signed correction exactly. Code:
[`conjecture_B_hub_correction.py`](../conjecture_B_hub_correction.py), 580 graphs.

**Headline.** The signed hub-correction is the **degree–Fiedler assortativity term**
`𝒜 = Σ_{ab∈E}(d_a−d_b)(f_a²−f_b²)`, which is **≤ 0 on 87% of graphs** (hub-flatness: across a
high-degree-gap edge the higher-degree endpoint has the smaller `f²`). The target rewrites as
`Open + 𝒜 ≥ λ₂fᵀAf` (580/580). But neither tool that could supply a *local* certificate works:
hub-flatness is ~40× too loose, and only 12% of the open energy is incident to the hubs. The slack
stays irreducibly global.

---

## TASK 1 — exact decomposition (verified; conventions fixed)

`fᵀAf = fᵀ(D−L)f = fᵀDf − λ₂fᵀf` (residual `5·10⁻¹⁴`; `= fᵀDf − λ₂` for unit `f`). Hence

> `Σ_v R_v f_v² = − 𝒜 + λ₂·fᵀAf`,  `𝒜 = Σ_{ab∈E}(d_a−d_b)(f_a²−f_b²)`  (residual `1·10⁻¹²`),

and the target becomes

> **`Open + 𝒜 ≥ λ₂·fᵀAf`**,  equivalently `Open + 𝒜 − λ₂fᵀAf = −Q ≥ 0`  (residual `7·10⁻¹²`, 580/580).

**Factor-2 conventions.** `fᵀAf = Σ_{a,b}A_{ab}f_af_b = 2Σ_{ab∈E}f_af_b`. `Open = ½Σ_v Open_v
= Σ_{induced P₃}(f_a−f_b)²`. `𝒜` is over **unordered** edges; the ordered double sum is `2𝒜`
(matching the formalised `degAssort_edge_identity`, which carries the `−½`).

## TASK 2 — degree/Fiedler anti-correlation

| quantity | value |
|---|---|
| `𝒜 ≤ 0` | **`504/580`** (`𝒜 ≥ 0` only `76`) |
| `𝒜` (min / median / max) | `−314` / `−16.2` / `0.93` |
| `𝒜 / (λ₂fAf)` (median) | `−3.49` |
| `𝒜 / Open` (median) | **`−0.556`** |

**`𝒜` contribution by `|degree gap|` quartile (pooled edges):**

| quartile | `|d_a−d_b|` | edges | Σ contribution |
|---|---|---|---|
| Q2 | `[0,2)` | 120 385 | `−78` |
| Q3 | `[2,5)` | 77 962 | `−930` |
| Q4 | `[5,79)` | 69 819 | **`−15 103`** |

`𝒜` is **negative and dominated by high-degree-gap edges** — exactly the hub-flatness signature:
where `d_a ≫ d_b`, the hub `a` has `f_a² < f_b²`, so `(d_a−d_b)(f_a²−f_b²) < 0`. The correction is
real, signed, and concentrated on hub-incident edges, and it is comparable in size to `Open` itself
(`𝒜/Open ≈ −0.56`).

## TASK 3 — hub-flatness as a credit (diagnostic only, NOT a certificate)

For the `R_v<0` hubs, compare the *actual* credit to the hub-flatness *upper bound*
(`f_v² ≤ d_v/(d_v−λ₂)²`):

| | median |
|---|---|
| `actual_hub_credit = Σ_{R<0}|R_v|f_v²` | `0.33` |
| `HF_upper_credit  = Σ_{R<0}|R_v|·d_v/(d_v−λ₂)²` | `4.86` |
| `actual / HF_upper` (min/median/max) | `0.000` / **`0.023`** / `0.49` |

Hub-flatness over-estimates the credit by **~40×** (median ratio `0.023`). Same verdict as the
earliest analysis: hub-flatness has the right *direction* but is far too loose to certify the hub
contribution. (`HF_upper` is only a diagnostic upper bound, never a proof certificate.)

## TASK 4 — open energy incident to the hubs

| test | holds |
|---|---|
| `Open_hub ≥ actual_hub_credit` | `486/580` |
| `Open_hub + actual_hub_credit ≥ Σ_{R>0}R_v f_v²` | **`28/580`** |
| `Open − Open_hub ≤ −Q` (slack) | `28/580` |
| `Open_hub / Open` (median) | **`0.123`** |

Only **12%** of the open-2-path energy is incident to the `R_v<0` hubs. So although `Open_hub`
usually clears the *hub's own* credit (`486/580`), it cannot also cover the positive demand
`Σ_{R>0}R_v f_v²` (fails `552/580`). The open energy lives on the low-degree, high-`f` vertices,
not on the hubs whose negativity we are trying to exploit.

## TASK 5 — manifestly-signed form for `Open + 𝒜 − λ₂fᵀAf`

This quantity **is** `−Q` (TASK 1), so any exact rewrite that is manifestly nonnegative would be a
proof of the conjecture. In edge form:

> `Open + 𝒜 − λ₂fᵀAf = Open + Σ_{ab∈E}[(d_a−d_b)(f_a²−f_b²) − 2λ₂ f_a f_b]`.

The per-edge bracket `(d_a−d_b)(f_a²−f_b²) − 2λ₂f_af_b` is **sign-indefinite** (no per-edge
positivity — a closed route anyway), and combining it with the open energy `Open = Σ_{induced P₃}
(f_a−f_b)²` mixes edge sums with 2-path sums over different index sets. **No sum-of-squares /
triple decomposition makes it manifestly nonnegative** — the cancellation between `Open` (on
non-edges through shared neighbours) and the negative hub edges of `𝒜` is genuinely global.

## Conclusion

The missing signed correction is identified exactly: the assortativity term `𝒜`, negative and
hub-concentrated. But the two natural local certificates both fail quantitatively:
- **hub-flatness** is ~40× too loose (TASK 3);
- **hub-incident open energy** is only 12% of `Open` and cannot cover the demand (TASK 4).

So the proof cannot be assembled from hub-local pieces. The slack `−Q = Open + 𝒜 − λ₂fᵀAf` requires
the open energy on the *low-degree* vertices to compensate, *across the graph*, the negative hub
edges of `𝒜` — a global cancellation with no edge/triple SOS. This sharpens, once more, that the
working argument must be a single global inequality preserving the degree–Fiedler sign structure
(hub-flatness direction) rather than any localisation.

## Formalised (Lean, `ConjectureB.lean`, no `sorry`)
- `quadForm_adjMatrix_fiedler` — `fᵀAf = fᵀDf − λ·fᵀf` (the quadratic form of the eigen-equation,
  the exact bridge `λ₂fᵀAf = λ₂(fᵀDf − λ₂)` used in TASK 1). Together with the already-formalised
  `degAssort_edge_identity` this gives the full exact decomposition `Σ_v R_v f_v² = −𝒜 + λ₂fᵀAf`.
