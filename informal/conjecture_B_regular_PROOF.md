# Conjecture B — COMPLETE PROOF for regular graphs

**Theorem.** For every connected `d`-regular graph `G`, the lift inequality holds: `T ≤ λ₂G`
(equivalently `gap = λ₂G − T ≥ 0`), with equality iff `G = K_n`. This is Conjecture B's energy
inequality (`conjectureB_lift`) on the regular case. The proof is elementary (a counting bound +
Cauchy interlacing). Verified: [`conjecture_B_regular_core.py`](../conjecture_B_regular_core.py).

## Setup

`G` connected `d`-regular, `n` vertices; `f` the unit Fiedler (`L_G f = λf`, `λ = λ₂ > 0`, `f ⊥ 1`).
Regular ⇒ `S = Σ_v d_v f_v = d·Σf_v = 0` and `fᵀDf = d`. Edge gradient `g_e = f_a − f_b`,
`Σ_{edge} g_e² = fᵀL_G f = λ`. Triangle energy `T = Σ_{edge} t_e g_e²` (`t_e = ` #common neighbours).

## Step 1 — the regular identity `gap = λ(n−λ) − C`

`t_e = (n−2) − deficit_e`, `deficit_e = #{c : c≁a or c≁b} = mdeg_a + mdeg_b − t̄_e`, where
`mdeg = n−1−d` and `t̄_e = ` #common **non**-neighbours. Regular ⇒ `deficit_e = 2(n−1−d) − t̄_e`, so
`Σ deficit_e g_e² = 2(n−1−d)λ − C` with `C := Σ_{edge} t̄_e g_e²`. Then `T = (n−2)λ − Σ deficit_e g_e²
= (2d−n)λ + C`, and (regular `λ₂G = λ(2d−λ)`):

> **`gap = λ(2d−λ) − T = λ(n−λ) − C`** (exact; verified to machine precision).

## Step 2 — the deficit bound `C ≤ (n−1−d)λ`

`t̄_e =` #common non-neighbours of `{a,b} ⊆` non-neighbours of `a`, which number `mdeg_a = n−1−d`
(`b` is a neighbour, not counted). So `t̄_e ≤ n−1−d` for every edge, giving

> **`C = Σ_{edge} t̄_e g_e² ≤ (n−1−d) Σ_{edge} g_e² = (n−1−d)λ`.**

## Step 3 — the spectral bound `λ₂ ≤ d+1` (Cauchy interlacing)

`G` has an edge `{u,v}`; the principal `2×2` submatrix of the adjacency `A` on `{u,v}` is
`[[0,1],[1,0]]`, with eigenvalues `±1`. **Cauchy interlacing** (`μ_i(A) ≥ μ_i(B)` for a principal
`k×k` `B`) gives `μ₂(A) ≥ μ₂([[0,1],[1,0]]) = −1`. For `d`-regular, `λ_i = d − μ_i(A)`, so
`λ₂ = d − μ₂(A) ≤ d − (−1) =`

> **`λ₂ ≤ d + 1`.** (Verified: 0 violations over 200 random regular graphs; tight at `K_n`, `λ₂=n=d+1`.)

## Step 4 — conclude

> **`gap = λ(n−λ) − C ≥ λ(n−λ) − (n−1−d)λ = λ(d+1−λ) ≥ 0`**,

since `λ ≤ d+1` (Step 3) and `λ > 0`. Hence `T ≤ λ₂G` for every connected regular graph. ∎

**Equality:** `gap = 0` forces `λ(d+1−λ) = 0` and `C = (n−1−d)λ`. With `λ > 0`, `λ = d+1`; for regular
`λ₂ = d+1` happens iff `μ₂(A) = −1`, which (interlacing tightness, all `2×2` edge blocks saturate) forces
`G = K_n`. (Verified: among all tested regular graphs, only `K_n` has `gap = 0`; complete multipartite
have `C = 0` but `λ < d+1`, so `gap = λ(d+1−λ) > 0`.)

## Verification table (sample)

| graph | n | d | λ | C | `(n−1−d)λ` | `λ(d+1−λ)` | gap |
|---|---|---|---|---|---|---|---|
| Petersen | 10 | 3 | 2.0 | 8.0 | 12.0 | 4.0 | 8.0 |
| Paley(13) | 13 | 6 | 4.70 | 14.1 | 28.2 | 10.8 | 24.9 |
| hypercube Q₄ | 16 | 4 | 2.0 | 16.0 | 22.0 | 6.0 | 12.0 |
| `K_{7,7}` | 14 | 7 | 7.0 | 0 | 42 | 7.0 | 49.0 |
| cycle C₂₀ | 20 | 2 | 0.098 | 1.57 | 1.66 | 0.28 | 0.38 |
| `K₂₀` | 20 | 19 | 20 | 0 | 0 | 0 | 0 (eq) |

All satisfy `gap ≥ λ(d+1−λ) ≥ 0` and `C ≤ (n−1−d)λ` and `λ ≤ d+1`.

## Significance and scope

- **This is a complete, elementary proof of Conjecture B's lift inequality `T ≤ λ₂G` for ALL connected
  regular graphs** — the *true* inequality (not the `B′` relaxation), with the complete graph as the
  unique equality case. It strictly covers the dense regime `λ ∈ (d, d+1]` where the old
  `aggregate_triangle_poincare_regular` bound (`T ≤ λ·d`) is *insufficient* (it needs `λ ≤ d`, false at
  `K_n`).
- The proof combines: the **complement/deficit identity** `gap = λ(n−λ) − C` (rounds on non-edge
  decomposition), the **counting bound** `t̄_e ≤ n−1−d`, and **Cauchy interlacing** `λ₂ ≤ d+1`.

## TASK 5 — the irregular correction

For non-regular `G`, `gap = Σ deficit_e g_e² − λΣ_{nonedge} h² − λS²/m`. The regular proof used
`mdeg ≡ n−1−d` (Step 2) and `λ₂ = d − μ₂` (Step 3); **both break for irregular graphs**:
- `Σ deficit_e g_e² = Σ_v mdeg_v D_v − C` with `mdeg_v` varying (no single factor).
- `λ₂ ≤ d+1` has no irregular analogue with a single `d`; the relevant bound is
  `λ₂ ≤ Δ+1` or finer, and the `−λS²/m` term (`= D`, the irregularity correction) must be absorbed.
From the correction-terms round, `D = λS²/m` is small (`≤ 0.23·Σdef`, `= 0` for regular). So the
irregular case is the regular proof **plus** controlling `mdeg`-variance and the `λS²/m` term — the
remaining open content, consistent with all prior findings (the bottleneck/irregular regime is the hard
part).

## Lean target (high value)

The regular proof is formalizable: (1) deficit identity `T = (2d−n)λ + C` (counting + `Σg²=λ`); (2)
`t̄_e ≤ n−1−d` ⇒ `C ≤ (n−1−d)λ`; (3) `λ₂ ≤ d+1` via Cauchy interlacing (`μ₂(A) ≥ −1` from a `2×2`
edge block); (4) `gap ≥ λ(d+1−λ) ≥ 0`. This would **upgrade `aggregate_triangle_poincare_regular` to a
complete regular `conjectureB_lift`** (covering the dense regime it currently misses). The interlacing
step (`μ₂ ≥ −1`) is the main new Mathlib ingredient.
