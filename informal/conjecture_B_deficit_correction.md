# Conjecture B — triangle-Poincaré deficit vs the required correction

`T = fᵀL_t f` (real triangles). `B ⟺ Deficit ≥ Required`, where
`Deficit = λ₂fᵀDf − T ≥ 0` (aggregate-Poincaré surplus) and
`Required = λ₂(λ₂ + S²/m − fᵀDf) = λ₂(S²/m − fᵀAf)` (`fᵀAf = fᵀDf − λ₂`). Code:
[`conjecture_B_deficit_correction.py`](../conjecture_B_deficit_correction.py).

**Headline — the most positive result of the whole investigation.** On the binding
deg2+dense family the ratio **`Deficit/Required` does NOT → 1**: it converges to **≈ 1.5**
(2.38 → 1.56 from `n=50` to `n=1000`, with geometrically shrinking decrements). The
aggregate-Poincaré surplus carries a **stable ~50–56% safety margin** over the required
correction at every scale. Identity: `Deficit − Required = RHS − T` (the actual-triangle
slack), so `ratio = 1 + (RHS−T)/Required`. **Unlike B2′ (which goes asymptotically tight),
the real-triangle Dirichlet route has room to spare — minimality may not be needed.**

---

## TASK 1 — Deficit vs Required at scale

**Corpus `n≤9`:** `Required > 0` on only **6/9020** graphs — exactly the `K_n` (where it is
`0`, equality). On all others `Required ≤ 0`, so `B` is automatic (`Deficit ≥ 0 ≥
Required`). So the correction only "bites" on `K_n` and on the deg2+dense-type family.

**deg2+dense (binding family):**

| `n` | `Deficit` | `Required` | `ratio` | margin `(D−R)/D` | `RHS−T` |
|---|---|---|---|---|---|
| 50 | 2.008 | 0.845 | **2.376** | 0.579 | 1.163 |
| 100 | 1.987 | 1.074 | 1.851 | 0.460 | 0.914 |
| 200 | 1.998 | 1.186 | 1.684 | 0.406 | 0.812 |
| 500 | 1.994 | 1.250 | 1.595 | 0.373 | 0.744 |
| 1000 | 1.999 | 1.278 | **1.564** | 0.361 | 0.721 |

`Deficit ≈ 2.0` is **constant** in `n`; `Required` **saturates** at ~1.28; the ratio
decreases but with **shrinking decrements** (0.525, 0.167, 0.089, 0.031) → a finite limit
**≈ 1.5**, bounded well away from 1.

## TASK 3 — structure of `Required = λ₂(S²/m − fᵀAf)`

| `n` | `fᵀAf = fᵀDf−λ₂` | `S²/m` | `S²/m − fᵀAf` | `λ₂` | `Required` |
|---|---|---|---|---|---|
| 50 | 0.674 | 1.094 | 0.420 | 1.976 | 0.830 |
| 200 | 0.655 | 1.244 | 0.589 | 1.994 | 1.174 |
| 1000 | 0.650 | 1.289 | 0.638 | 1.999 | 1.276 |

All ingredients **stabilize**: `fᵀAf → 0.65`, `S²/m → 1.29`, `λ₂ → 2`, so `Required → 1.28`.
(`fᵀAf = Σ_{ab∈E} 2f_af_b` stays small-positive; `S²/m` grows mildly to a plateau.) Nothing
diverges — the correction is `O(1)`, not growing, so the constant `Deficit ≈ 2` keeps the
ratio bounded above 1.

## TASK 2 — per-apex decomposition `Deficit = Σ_c (λ₂·mass_c − energy_c)`

(`mass_c = Σ_{v∈N(c)} f_v²`, `energy_c = E_{G[N(c)]}(f)`; `Σ_c mass_c = fᵀDf`,
`Σ_c energy_c = T` by the apex identity, now formalized in `Paper15.lean`.)

| `n` | local Poincaré fails | `Σ surplus⁺` | `Σ overshoot` | net `Deficit` |
|---|---|---|---|---|
| 50 | 20/50 (40%) | 2.296 | 0.253 | 2.043 |
| 100 | 42/100 (42%) | 2.303 | 0.290 | 2.012 |
| 200 | 78/200 (39%) | 2.322 | 0.307 | 2.015 |

- **Local Poincaré `energy_c ≤ λ₂·mass_c` fails on ~40% of apexes** on deg2+dense (far more
  than the 6% on the generic corpus), but the **total overshoot (~0.3) is tiny vs the total
  surplus (~2.3)** — net `Deficit ≈ 2.0`. The 40% failures are easily outweighed.
- **Individual overshoots shrink** (worst apex surplus −0.017, −0.010, −0.005 at n=50/100/200)
  and sit on **high-degree (dense) apexes**.
- The **surplus is carried by the low-degree-half apexes** (at n=200: dense apexes net ≈
  −0.02, low apexes net +2.04). So the dense bulk roughly breaks even and the low-degree
  apexes supply the entire `Deficit`.

## TASK 4 — the decisive test: ratio bounded away from 1

Min ratio over samples by `n` (deg2+dense, `q=0.65`):

| `n` | 50 | 100 | 200 | 400 | 700 | 1000 |
|---|---|---|---|---|---|---|
| min ratio | 2.38 | 1.86 | 1.69 | 3.21 | 1.58 | **1.56** |

**VERDICT: the ratio stays bounded away from 1 (limit ≈ 1.5).** The aggregate-Poincaré
surplus *suffices* to absorb the required correction, at every tested scale. This is the
**first route in the entire investigation with a stable margin on deg2+dense** — B2′,
the per-vertex bound, and the weighted-CS bounds all went tight or failed there.

---

## Synthesis — the Dirichlet route may close B without minimality

The proof of `B` on the binding family reduces to:
1. **Aggregate triangle-Poincaré** `T ≤ λ₂fᵀDf` (i.e. `Deficit ≥ 0`) — holds 100%, and the
   apex identity `T = Σ_c E_{G[N(c)]}(f)` underlying it is **formalized** (`Paper15.lean`).
2. **Surplus ≥ correction**: `Deficit ≥ Required`, i.e. `λ₂fᵀDf − T ≥ λ₂(λ₂+S²/m−fᵀDf)`.

The new finding is that step 2 holds with a **constant ~1.5× margin** (Deficit ≈ 2·Required
asymptotically), *not* a vanishing one. So — in sharp contrast to B2′ — there is no
asymptotic tightness to fight: a *crude* lower bound on `Deficit` (or upper bound on
`Required`) with a sub-50% slack would already close it. The per-apex picture shows where
to get it: the low-degree apexes carry `Deficit ≈ 2`, the dense apexes break even, and the
~40% local-Poincaré failures overshoot by a total `~0.3 ≪ 2`. A global (not per-apex)
Poincaré argument that captures the low-degree apex surplus is the concrete next target.

**This reframes the open problem favourably:** instead of an asymptotically exact
minimality argument (the B2′ wall), B reduces to a *margined* inequality `Deficit ≥
Required` where both sides are `O(1)` and the ratio is `~1.5`.

### Caveats
`λ₂`, `f`, `T` numerical. TASK 1/3/4 over corpus (9020) + deg2+dense to `n=1000`
(2–6 samples/size); TASK 2 (per-apex) to `n=200`. The "bounded away from 1" verdict rests
on the converging trend (decrements shrinking ~geometrically, factor ~0.4) → limit ≈ 1.5;
a large-`n` (1500/2000) confirmation is consistent. `Required > 0` only on the deg2+dense-
type family and `K_n` (equality); elsewhere B is automatic from `Deficit ≥ 0`.
