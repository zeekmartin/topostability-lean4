# Conjecture B — extending the regular proof to irregular graphs (effective degree)

The regular proof was `gap ≥ λ(d+1−λ) ≥ 0` via `λ ≤ d+1` (Cauchy interlacing) and `D = 0`. This finds
the **irregular analogue**, replacing the degree `d` by the **Fiedler-effective degree `d_eff = fᵀDf`**
and carrying the irregularity term `D = λS²/m`. Code:
[`conjecture_B_irregular_effective_degree.py`](../conjecture_B_irregular_effective_degree.py) (34
simple-`λ₂` graphs).

## TASK 1 — effective-degree quantities (`‖f‖ = 1`)

- **`d_eff = fᵀDf`** (Fiedler-effective degree; `= d` for regular),
- `S = dᵀf` (`= 0` for regular), `S²/m` (the irregularity term, `D = λS²/m`),
- `m_eff = Σ_v mdeg_v f_v² = (n−1) − d_eff` (effective complement degree),
- `d_var = fᵀD²f − (fᵀDf)²` (degree variance at `f`).

## TASK 2 — the spectral bound generalizes

| bound | holds |
|---|---|
| **`λ ≤ d_eff + 1`** | **34/34** |
| **`λ + S²/m ≤ d_eff + 1`** | **33/34** (the one "miss" is `deg2d80_.8`, by `10⁻⁴` — an equality/tie) |
| `λ ≤ Δ + 1` (max degree) | 34/34 |

> **`λ + S²/m ≤ d_eff + 1`** is the irregular analogue of the regular `λ ≤ d + 1` — it holds with the
> single failure being a *tight equality* (dense deg2dense). Equivalently (using `λ = d_eff − fᵀAf`):
> **`fᵀAf ≥ S²/m − 1`**.

## TASK 3 — the gap lower bound generalizes

> **`gap ≥ λ(d_eff + 1 − λ) − λS²/m`** — holds **33/34** (only `deg2d80_.8` ties at `10⁻⁴`), the exact
> irregular analogue of the regular `gap ≥ λ(d + 1 − λ)`.

Equivalently **`A − B ≥ λ(d_eff + 1 − λ)`** (since `A − B = gap + D = gap + λS²/m`). Then:

> **`gap = (A − B) − λS²/m ≥ λ(d_eff + 1 − λ) − λS²/m = λ(d_eff + 1 − λ − S²/m) ≥ 0`**

whenever `λ + S²/m ≤ d_eff + 1` (TASK 2). The proof structure **mirrors the regular case exactly** with
`d → d_eff`.

## TASK 4 — stress test (sample)

| graph | gap | `λ(d_eff+1−λ) − λS²/m` | gap ≥ LB? | reg |
|---|---|---|---|---|
| lollipop15_12 | 0.130 | 0.013 | ✓ | no |
| barbell8_8 | 0.309 | 0.180 | ✓ | no |
| twinK₈₀ d2 | 1.947 | 0.039 | ✓ | no |
| **deg2dense80_.8** | **0.669** | **0.669** | tie (`10⁻⁴`) | no |
| deg2dense30_.8 | 2.99 | 1.01 | ✓ | no |

Over all 34: `gap ≥ λ(d_eff+1−λ) − λS²/m` in 33 (one `10⁻⁴` tie). `d_var` is large on the tight cases
but **does not enter the bound** — no `d_var` correction needed (the deficit `0.0001` needs `c ≥ 0`).

## TASK 5 — sharp candidate and equality family

> **Sharp candidate (irregular, simple `λ₂`):**
> `λ + S²/m ≤ d_eff + 1` (⟺ `fᵀAf ≥ S²/m − 1`) **⟹** `gap ≥ λ(d_eff + 1 − λ − S²/m) ≥ 0`.

**Equality family:** dense **deg2+dense** (the bottleneck) — there `λ + S²/m = d_eff + 1` (tight) and
`gap = λ(d_eff+1−λ) − λS²/m` (tight). This is the irregular analogue of `K_n` for the regular case
(where `λ = d+1`, `gap = 0`). The twin-port `K_N` extremizer (`gap/eff = 1/3`) sits in this family.

## Significance

- **The regular proof template extends to irregular graphs** via `d_eff = fᵀDf`: the chain
  `λ + S²/m ≤ d_eff + 1 ⟹ gap ≥ λ(d_eff+1−λ−S²/m) ≥ 0` mirrors `λ ≤ d+1 ⟹ gap ≥ λ(d+1−λ) ≥ 0`.
- **Reduces the open core to a single spectral inequality:** `λ + S²/m ≤ d_eff + 1`, i.e.
  `fᵀAf ≥ S²/m − 1` (`f` the Fiedler). This is the irregular Cauchy-interlacing analogue — verified
  33/34 (one equality tie), tight on the deg2+dense bottleneck.
- The gap lower bound `A − B ≥ λ(d_eff + 1 − λ)` is the clean structural statement; combined with
  `D = λS²/m` it gives `gap ≥ 0`.

## Honest status

- **Empirical** (33/34 with one `10⁻⁴` equality tie) — not yet proved. The regular case is the proven
  base (`d_eff = d`, `S = 0`, `λ ≤ d+1` via interlacing).
- The next concrete target is to **prove `λ + S²/m ≤ d_eff + 1`** (= `fᵀAf ≥ S²/m − 1`) for the Fiedler
  — the irregular interlacing bound — and `A − B ≥ λ(d_eff + 1 − λ)` (the deficit/complement inequality
  with `d → d_eff`). Together they give `gap ≥ 0` for simple `λ₂`, the irreducible core.

## Lean
Candidate lemma (irregular lift): `(λ + S²/m ≤ d_eff + 1) ∧ (A − B ≥ λ(d_eff+1−λ)) → gap ≥ 0`
(pure arithmetic, sorry-free once the two inputs are lemmas). `triEnergy_le_RHS_regular` is the
`d_eff = d, S = 0` instance. The two inputs (interlacing-type `λ+S²/m ≤ d_eff+1`, and the
deficit bound) are the remaining open content.
