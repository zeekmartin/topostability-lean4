# Conjecture B — carrier-vertex surplus generalization

Carriers `H = {v : f_v² ≥ 1/n}`. `CSurplus(v) = Σ_{c∈N(v)} surplus_c = (A·surplus)_v`,
`surplus_c = λ₂·mass_c − energy_c`. `β(v) = CSurplus(v)/f_v²`. `Deficit = Σ_c surplus_c =
λ₂fᵀDf − T`; `Required = λ₂(λ₂+S²/m−fᵀDf)`; `B ⟺ Deficit ≥ Required`. Code:
[`conjecture_B_carrier_surplus.py`](../conjecture_B_carrier_surplus.py).

**Headline — the regime split is now exact.** `Required > 0` **only** in the
concentrated-Fiedler (bottleneck/irregular) regime, where a **dominant carrier exists** and
**accounts for ~100% of the Deficit**. On **every** spread-Fiedler family (regular, ER,
bipartite, Watts–Strogatz) **`Required ≤ 0`, so B is trivial** (`Deficit ≥ 0 ≥ Required`)
— the carrier mechanism is *moot* there. So Conjecture B splits cleanly:

> **(i) spread regime (`Required ≤ 0`):** B from the aggregate Poincaré `Deficit = λ₂fᵀDf −
> T ≥ 0` alone.
> **(ii) bottleneck regime (`Required > 0`):** B from the surplus of the carrier(s) at the
> Fiedler-concentration vertex.

Both use only the **eigen-equation + hub-flatness**, never `λ₂`-minimality.

---

## TASK 4 — spread-Fiedler families: `Required ≤ 0`, B is free

| family | regular? | `Deficit` | `Required` |
|---|---|---|---|
| Petersen (3-reg) | yes | 6.00 | **−2.00** |
| circulant 4-reg | yes | 0.22 | −0.31 |
| ER n=50 p=.3 | no | 16.4 | **−5.00** |
| ER n=50 p=.5 | no | 134.6 | −53.1 |
| `K_{4,4}` | yes | 16.0 | **−0.00** |
| `K_{5,5}` | yes | 25.0 | −0.00 |
| WS n=50 k=8 p=.3 | no | 11.6 | −10.5 |

**`Required ≤ 0` on all of them**, so `B` follows from `Deficit ≥ 0` (the aggregate
triangle-Poincaré `T ≤ λ₂fᵀDf`) with no further work. Algebra: `Required = λ₂(λ₂ + S²/m −
fᵀDf)`; for `d`-regular `fᵀDf = d`, `S = 0`, so `Required = λ₂(λ₂ − d) ≤ 0` (since `λ₂ ≤
d`); complete-bipartite `K_{m,n}` sits exactly at `Required = 0`. **`Required > 0` requires
`fᵀDf < λ₂ + S²/m`, i.e. the irregular/bottleneck structure** where the Fiedler concentrates
— precisely where a dominant carrier appears.

## TASK 2 — the dominant carrier explains the whole Deficit (bottleneck regime)

deg2+dense (the binding family, `Required > 0`):

| `n` | `Deficit` | `Required` | `#carriers` | `Σ_H CSurplus` | carrier fraction |
|---|---|---|---|---|---|
| 50 | 2.043 | 0.830 | 1 | 1.967 | 0.96 |
| 200 | 2.015 | 1.174 | 1 | 1.991 | 0.99 |
| 500 | 1.994 | 1.250 | 1 | 1.997 | **1.00** |

There is a **single carrier** (the degree-2 bottleneck vertex `v₀`, `f_{v₀}² ≈ 1`), and its
`CSurplus(v₀) = Σ_{c∈N(v₀)} surplus_c` accounts for **96–100% of the Deficit**. (No
double-counting issue — one carrier.) `β(v₀) = CSurplus(v₀)/f_{v₀}² ≈ λ₂`.

## TASK 1 — β by carrier degree

| family | `d_v=2` | `d_v=3` | `d_v=4` | `d_v=5` | `d_v=6` |
|---|---|---|---|---|---|
| corpus median β | 2.22 | 5.57 | 12.30 | 25.80 | 46.32 |
| deg2+dense | **2.00** | – | – | – | – |

- **`β` grows strongly with `d_v`** (corr `+0.71` pooled over 21 269 carriers); it is *not*
  a universal constant.
- **`β ≈ λ₂` holds only for degree-2 carriers** (the bottleneck case). deg2+dense:
  `β = 2.00…2.01` across `n`, matching `λ₂ ≈ 2`.
- For higher `d_v`, `β` is much larger (CSurplus sums apex-surplus over all `d_v`
  neighbours, each `≈ λ₂·f_v²`, so `β ~ d_v·λ₂ − (energy term)/f_v²` grows).
- **Rare negatives:** 3/21 269 carriers (all `d_v=3`) have `β < 0` (min −0.60) — so a naive
  "every carrier contributes positive surplus" lemma is *false*; it holds in aggregate and
  in the bottleneck regime, not per-carrier universally.

## TASK 3 — what determines β

| carrier | `λ₂` | `d_v` | `f_v²` | `β` | `β/λ₂` | `2(λ₂−1)` |
|---|---|---|---|---|---|---|
| deg2+dense n=100 | 1.988 | 2 | 0.989 | 2.005 | 1.008 | 1.977 |
| deg2+dense n=500 | 1.998 | 2 | 0.998 | 2.001 | 1.002 | 1.996 |

For the dominant degree-2 carrier, **`β/λ₂ ≈ 1.00`** (and `β ≈ 2(λ₂−1)` fits equally, since
`λ₂ ≈ 2` makes them coincide). No single clean formula works across degrees: `β` scales
roughly with `d_v` (summing surplus over `d_v` apex-neighbours), modulated by the
neighbourhood triangle-energy. The clean, decision-relevant fact is the **bottleneck case
`d_v = 2`: `β ≈ λ₂`**, giving `CSurplus(v₀) = β·f_{v₀}² ≈ λ₂·f_{v₀}² ≈ Deficit`.

---

## Synthesis — a clean, minimality-free two-regime proof skeleton

The carrier analysis completes the structural picture and yields an **exact regime split by
the sign of `Required = λ₂(λ₂ + S²/m − fᵀDf)`**:

1. **`Required ≤ 0` (spread / near-regular / dense):** `B` is immediate from `Deficit =
   λ₂fᵀDf − T ≥ 0`, i.e. the **aggregate triangle-Poincaré** `T ≤ λ₂fᵀDf`. This is the
   provable-looking lemma (built on the formalized apex identity, `Paper15.lean`), and it
   covers *all* the spread families tested (regular, ER, bipartite, WS).

2. **`Required > 0` (bottleneck / concentrated Fiedler):** the Fiedler concentrates on a
   low-degree vertex `v₀`, which is a **dominant carrier** whose `CSurplus(v₀) ≈ λ₂·f_{v₀}²`
   **accounts for ~100% of the Deficit**, and `λ₂·f_{v₀}² ≥ Required` with margin (β ≈ λ₂,
   `f_{v₀}² ≈ 1`). The `β ≈ λ₂` here is exactly the `ε = ½` / `λ₂ ≈ d_{v₀}` bottleneck
   mechanism of the apex-surplus round — eigen-equation + hub-flatness, no minimality.

This is the most complete and favourable framing reached: **B reduces to two
eigen-equation/hub-flatness facts, partitioned by a single explicit sign condition** — with
the hard, asymptotically-tight B2′ wall entirely bypassed.

### Caveats
`λ₂`, `f`, per-apex energies numerical. deg2+dense `q=0.65` `n≤500`; corpus `n≤9` (21 269
pooled carriers); ER/WS/regular/bipartite/Petersen as listed. `β` grows with `d_v` and is
not a clean closed form away from `d_v=2`; the regime-split conclusion rests on the sign of
`Required`, which is exact. The carrier picture is verified to explain the Deficit only in
the single-bottleneck family; multi-bottleneck graphs (several low-degree carriers) are the
natural next test.
