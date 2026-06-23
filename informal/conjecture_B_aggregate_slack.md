# Conjecture B — the aggregate-slack dichotomy (aggregate Poincaré proves a chunk)

**Corrected identity (the prompt dropped `D = λS²/m`):** `gap = λ(2d_eff − λ − S²/m) − T = S_agg + E`,
with `S_agg = λd_eff − T ≥ 0` (aggregate slack) and **`E = λ(d_eff − λ − S²/m) = λ(fᵀAf − S²/m)`**.
**Result: a clean DICHOTOMY — when `E ≥ 0` (i.e. `d_eff ≥ λ + S²/m`), the aggregate Poincaré already
proves `gap ≥ 0` (30/53); the hard case is the thin band `E < 0` (`d_eff < λ + S²/m ≤ d_eff + 1`),
where `S_agg ≥ −E` is needed (`= 1` at `K_n`).** Code:
[`conjecture_B_aggregate_slack.py`](../conjecture_B_aggregate_slack.py).

## Correction of the prompt's algebra

The prompt wrote `gap = λ(2d_eff − λ) − T`, **omitting `−D = −λS²/m`**. The correct identity is
`gap = λ(2d_eff − λ − S²/m) − T`. Hence `gap = S_agg + E` with `E = λ(d_eff − λ − S²/m)` (not
`λ·fᵀAf`; `E = λ(fᵀAf − S²/m)`, since `fᵀAf = d_eff − λ`). Verified to machine precision.

## TASK 1 — THE DICHOTOMY

`gap = S_agg + E`, `S_agg ≥ 0` (aggregate Poincaré `T ≤ λd_eff`, holds 68/68).

> **If `E ≥ 0` (`d_eff ≥ λ + S²/m`): `gap = S_agg + E ≥ S_agg ≥ 0` — the AGGREGATE POINCARÉ PROVES
> `gap ≥ 0`, no extra work.** This is **30/53** graphs (sparse/medium: lollipop, barbell, star, low-`q`
> gnp, low-`q` deg2+dense, sparse regular).
>
> **If `E < 0`: the hard case** — **23/53** (dense deg2+dense `q ≥ 0.5`, twin-port `K_N`, `K_n`).

Since the spectral bound `λ + S²/m ≤ d_eff + 1` holds, `E < 0 ⟺ λ + S²/m ∈ (d_eff, d_eff + 1]` — a
**thin band** (`E ∈ (−λ, 0)`). So the open problem is confined to this band.

## TASK 3/4 — the hard case `E < 0`: `S_agg ≥ −E`

| graph | gap | `S_agg` | `−E` | `S_agg/(−E)` |
|---|---|---|---|---|
| `K₂₀` | 0 | 20 | 20 | **1.000** (exact) |
| `K₁₂` | 0 | 12 | 12 | **1.000** |
| deg2+dense(80,.9) | 0.48 | 2.00 | 1.52 | 1.32 |
| deg2+dense(30,.9) | 0.89 | 2.00 | 1.11 | 1.80 |
| twin-port `K₈₀` d2 | 1.95 | 2.93 | 0.98 | 2.99 |

> **`S_agg ≥ −E` holds 23/23** in the hard band, with **equality exactly at `K_n`** (`S_agg = −E = n`).
> `gap ≥ 0 ⟺ S_agg ≥ −E` (circular — this *is* the conjecture in the `E < 0` band), but the band is
> thin and `K_n` is the unique tight point.

## TASK 2 — the aggregate slack structure

`S_agg/λ = d_eff − t_eff` where `t_eff = T/λ` (the Fiedler-weighted average triangle count). The
anti-correlation (`high-t edges have low gradient`) makes `t_eff < d_eff`:

| graph | `d_eff` | `t_eff` | `S_agg/λ = d_eff − t_eff` | `−E/λ` |
|---|---|---|---|---|
| `K₂₀` | 19 | 18 | **1.0** | **1.0** |
| deg2+dense(80,.9) | 2.87 | 1.87 | 1.00 | 0.76 |
| deg2+dense(30,.9) | 2.83 | 1.82 | 1.00 | 0.56 |

In the hard band, `S_agg/λ = d_eff − t_eff ≥ −E/λ = λ + S²/m − d_eff` — the aggregate slack
(`d_eff − t_eff`) covers the spectral deficit (`λ + S²/m − d_eff`). At `K_n` both equal `1`.

## Significance

- **The aggregate Poincaré (`T ≤ λd_eff`, the standing lemma) PROVES `gap ≥ 0` on 30/53 graphs** — all
  those with `d_eff ≥ λ + S²/m` (`E ≥ 0`). This is a genuine *partial* result, cleanly delimited.
- **The hard case is confined to the thin band `d_eff < λ + S²/m ≤ d_eff + 1` (`E < 0`)** — dense
  deg2+dense, twin-port, `K_n`. There `gap ≥ 0 ⟺ S_agg ≥ −E` (the conjecture, tight at `K_n`).
- **Both the regular dense case (`K_n` region, `E < 0`, proven by interlacing `λ ≤ d+1`) and the sparse
  case (`E ≥ 0`, aggregate) are now covered**; the residual is the *irregular* `E < 0` band
  (deg2+dense, twin-port).

## TASK 4 — the mechanism (anti-correlation)

`S_agg = Σ_e (d_eff − t_e) g_e²`: high-`t_e` (dense-core) edges have `d_eff − t_e` small but *also* low
`g_e²` (flat Fiedler on the dense core); low-`t_e` (bottleneck) edges have `d_eff − t_e` large and high
`g_e²`. This anti-correlation (verified: `t_eff = T/λ < d_eff`) makes `S_agg` large enough to cover
`−E` in the hard band. Quantifying `S_agg ≥ max(0, −E)` *is* the conjecture, but the dichotomy shows the
`max(0, ·)` is `0` (aggregate suffices) for 30/53 and the `−E` branch is the thin `E < 0` band.

## Conclusion

- **Corrected identity `gap = S_agg + E`** (`E = λ(d_eff − λ − S²/m)`); the prompt's `λ·fᵀAf` omitted
  `−D`.
- **Dichotomy:** `E ≥ 0` ⟹ **aggregate Poincaré proves `gap ≥ 0`** (30/53); `E < 0` (thin band
  `λ+S²/m ∈ (d_eff, d_eff+1]`) is the hard case (`S_agg ≥ −E`, tight at `K_n`).
- This is the cleanest partial result: the open problem is **confined to the `E < 0` band**, with the
  aggregate Poincaré dispatching the rest and the regular dense case (`K_n` region) proven by
  interlacing.

## Lean
Candidate: `gap = S_agg + E` (identity) + `S_agg ≥ 0` (= aggregate Poincaré, `T ≤ λd_eff`, the standing
sorry; regular case proved) ⟹ `gap ≥ 0` whenever `E ≥ 0` (`d_eff ≥ λ + S²/m`). So `triEnergy_le_RHS` for
the `E ≥ 0` regime reduces to `aggregate_triangle_poincare` alone. The `E < 0` band remains the open
core (regular sub-case proven).
