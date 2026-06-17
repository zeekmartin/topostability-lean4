# Conjecture B — spectral neighborhood bounds for the apex energy: FAIL

Using `T = Σ_c E_{G[N(c)]}(f)` (formalized, `Paper15`), bound each apex energy
`energy_c = (f−mean_c)ᵀ L_{H_c} (f−mean_c) ≤ λ_max(L_{H_c})·var_c` (Rayleigh), with
`var_c = Σ_{v∈N(c)}(f_v−mean_c)²`, against Poincaré `λ₂(G)·mass_c`. Code:
[`conjecture_B_spectral_neighborhood.py`](../conjecture_B_spectral_neighborhood.py).

**Headline: no spectral neighborhood bound closes B.** The only *valid* per-apex bound is
Rayleigh `λ_max·var` (0 violations), but it aggregates **24× too loose** on deg2+dense and
**does not beat Poincaré on dense apices** (`λ_max·var = 1.28` vs `λ₂·mass = 0.118`, ~10×
worse). The reason is structural: on the carrier apices the Fiedler restricted to `N(c)` is
a **low-Rayleigh vector concentrated on a near-pendant** (the bottleneck vertex), so
`energy_c ≈ var_c`, while `λ_max(L_{H_c}) ≈ d_c` reflects the dense bulk — the bound loses a
factor `d_c`. The hybrid `min(λ_max·var, λ₂·mass)` is both **invalid** (it can undershoot
`energy_c` on Poincaré-failing apices) and **fails** (1.20 on deg2+dense).

---

## TASK 1 — per-apex local bounds (3690 apices)

| bound | violations |
|---|---|
| **(a) `energy ≤ λ_max·var`** (Rayleigh) | **0** ✓ (the only valid one) |
| (b) `energy ≤ λ₂·mass` (local Poincaré) | 221 (6.0%) |
| (c) `energy ≤ λ₂·var` | 1540 (**41.7%**) |
| (d) `energy ≤ density·d·var` | 261 (7.1%) |

Only the Rayleigh bound `λ_max·var` is universally valid. `λ₂·var` fails 42% (variance is
too small relative to energy on many apices). `λ₂·mass` fails the known 6%.

## TASK 2 / 4 — aggregates vs RHS (per family, max ratio)

| family | # | `Σλ_max·var/RHS` | `Σλ₂·var/RHS` | `Σλ₂·mass/RHS` | **`hybrid/RHS`** | `T/RHS` |
|---|---|---|---|---|---|---|
| corpus | 400 | 3.00 | 1.33 | 1.50 | 1.00 | 1.00 |
| deg2+dense | 2 | **24.4** | 0.96 | 1.25 | **1.20** | 0.77 |
| lollipop | 4 | 5.06 | 0.05 | 1.98 | 0.12 | 0.09 |
| circulant | 2 | 0.89 | 0.04 | 0.51 | 0.27 | 0.21 |
| ER / WS | 3 | 0.7–1.6 | 0.2–0.8 | 0.6–0.9 | 0.4–0.8 | 0.1–0.4 |

- **`Σλ_max·var` (the valid Rayleigh aggregate) is hopelessly loose** — 24× on deg2+dense,
  3× on corpus, 5× on lollipops. Valid but useless.
- `Σλ₂·mass = λ₂·fᵀDf` (the aggregate Poincaré, valid as a *global* bound on `T`) overshoots
  RHS (1.25–1.5), as known.
- `Σλ₂·var` is small (0.04–1.33) but **not a valid bound** (42% per-apex violations).
- **Hybrid `T_hybrid = Σ min(λ_max·var, λ₂·mass) ≤ RHS` closes only 412/414** — fails on the
  2 deg2+dense graphs (max **1.20**). Worse, the hybrid `min` is **not a valid upper bound
  on `T`**: where local Poincaré fails (6%), `min` may equal `λ₂·mass < energy_c`, so
  `T_hybrid` can *undershoot* `T`. So even closing it would not prove `T ≤ RHS`.

## TASK 3 — does `λ_max·var` beat Poincaré on dense apices? NO

| family | dense apices | mean `λ_max·var` | mean `λ₂·mass` | `spec < poin` |
|---|---|---|---|---|
| deg2+dense n=50 | 22 | **1.28** | **0.118** | 27% |

On dense apices `λ_max·var` is **~10× larger** than `λ₂·mass` — the spectral bound is
*worse*, not better. The hoped "flat Fiedler ⇒ small variance ⇒ small `λ_max·var`" does not
materialise on the apices that carry `T`: there `N(c)` contains the bottleneck vertex `v₀`
(`f≈1`) as an **outlier**, so `var_c ≈ mass_c` (the outlier dominates the variance), while
`λ_max(L_{H_c}) ≈ d_c` (dense bulk) — giving `λ_max·var ≈ d_c·mass_c`, a factor `d_c` worse
than `energy_c`.

## Why it fails structurally

For a carrier apex `c` (neighbour of the bottleneck `v₀`), `v₀ ∈ N(c)` is a **near-pendant
in `H_c = G[N(c)]`** (it connects only to the other bottleneck neighbour `b` inside `N(c)`).
So `f|_{N(c)}` is a vector that is large on a near-pendant and ~0 on the dense bulk:
`energy_c ≈ (f_{v₀}−f_b)² ≈ f_{v₀}²` and `var_c ≈ f_{v₀}²`, giving **Rayleigh quotient
`energy_c/var_c ≈ 1`** — far below `λ_max(L_{H_c}) ≈ d_c`. The Rayleigh *upper* bound
`λ_max·var` cannot see that `f|_{N(c)}` is a low-Rayleigh vector; it charges the full
`λ_max`. (Using `λ₂(H_c)` as a lower bound doesn't help — energy needs an *upper* bound.)

---

## Synthesis — the spectral-neighborhood route is closed

- The only valid per-apex spectral bound, Rayleigh `λ_max·var`, is **24× too loose** in
  aggregate and **does not beat Poincaré on dense apices**. Variance-based bounds (`λ₂·var`,
  `density·d·var`) are invalid (40%/7% violations).
- The hybrid `min` is both invalid (can undershoot `T`) and fails numerically (1.20).
- **Root cause:** on the carrier apices the energy is set by an *outlier* (the bottleneck
  vertex as a near-pendant in `H_c`), which inflates `var_c` and is invisible to
  `λ_max(L_{H_c})`. No neighborhood spectral quantity (`λ_max`, `var`, `λ₂(H_c)`) captures
  it; only `λ₂(G)·mass_c` is tight there (ratio ≈ 0.5), but its aggregate overshoots `RHS`
  and it fails the 6% elsewhere.

This exhausts the spectral-neighborhood family. The recurring obstruction is unchanged: the
**carrier/bottleneck apices** (Fiedler outlier on a low-degree vertex) defeat every per-apex
bound — Poincaré is tight but globally over-counts; Rayleigh and variance bounds blow up on
the outlier. The viable directions remain the **global** ones already identified: the exact
`Deficit ≥ Required` margin (stable ≥ 1.7) with the `sign(Required)` split, and the
carrier-surplus argument for the unequal-degree bottleneck (which itself does not generalise
to separated mass/triangle structure). No single per-apex lemma has closed the
`Required > 0` regime.

### Caveats
`λ₂`, `f`, neighborhood spectra numerical. 414 graphs (corpus n≤9 sample + deg2+dense n≤100
+ lollipop/barbell/chain/circulant/ER/WS); deg2+dense capped at n=100 (per-apex
`eigvalsh` cost). Rayleigh (a) is exact-valid (0/3690); the 2 hybrid failures are deg2+dense.
`T ≤ RHS` (B) holds throughout.
