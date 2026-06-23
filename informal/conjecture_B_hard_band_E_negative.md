# Conjecture B — the hard band `E < 0` IS regime ii (a unifying synthesis)

**Key identity: `Required = λ(λ + S²/m − d_eff) = −E`.** So **`E < 0 ⟺ Required > 0`**: the
aggregate-slack dichotomy (`gap = S_agg + E`) is *exactly* the original regime-i / regime-ii split.
**Result: the hard band `E < 0` (regime ii) decomposes as `regular ∪ TYPE A` (no residual); the easy
band `E ≥ 0` (regime i) is dispatched by the aggregate Poincaré. The whole conjecture-B program maps
onto the `E`-sign.** Code:
[`conjecture_B_hard_band_E_negative.py`](../conjecture_B_hard_band_E_negative.py).

## The unifying identity

`Required := λ(λ + S²/m − fᵀDf) = λ(λ + S²/m − d_eff) = −E` (verified to machine precision). Hence:

> **`E ≥ 0 ⟺ Required ≤ 0` (regime i)**, and **`E < 0 ⟺ Required > 0` (regime ii)**.

The aggregate-slack decomposition `gap = S_agg + E` is therefore the regime split in new clothing:
`gap = S_agg − Required`.

## TASK 1/5 — coverage of `E < 0` (= regime ii): `regular ∪ TYPE A`

Of 47 graphs, **29 have `E < 0`** (regime ii). Their classification:

| class | count | status |
|---|---|---|
| **regular** (`K_n`, dense regular) | 3 | **PROVEN** (`triEnergy_le_RHS_regular`, interlacing `λ ≤ d+1`) |
| **TYPE A** (deg2+dense, twin-port; low-degree vertex bottleneck) | 26 | extremality program (`gap/eff ≥ 1/3`, 3 rigour items) |
| other | **0** | — |

> **The `E < 0` band is entirely `regular ∪ TYPE A`** — no residual category. (Near-complete irregular
> `K_n − k` turned out to be `E ≥ 0`, i.e. regime i, handled by the aggregate.) **`TYPE B`
> path-bottlenecks (lollipop/barbell) are `E ≥ 0` (regime i)** — `λ` small there, so the aggregate
> Poincaré covers them too.

## TASK 2 — asymptotics in `E < 0`

| graph | `S_agg` | `−E = Required` | ratio | gap | `λ/d_eff` |
|---|---|---|---|---|---|
| `K_n` | `n` | `n` | **1.000** | 0 | `≈1.05` |
| deg2+dense(80,.9) | 2.00 | 1.52 | 1.32 | 0.48 | 0.70 |
| twin-port `K₈₀` d2 | 2.93 | 0.98 | 2.99 | 1.95 | 0.21 |

`ratio = S_agg/(−E) ≥ 1` (= `gap ≥ 0`), **`= 1` exactly at `K_n`**. `S_agg → 2` for deg2+dense (the
attachment), `→ d`-dependent for twin-port.

## TASK 3 — structure of `E < 0`

`E < 0 ⟺ λ + S²/m > d_eff` — `λ` (plus the degree-Fiedler term `S²/m`) exceeds the effective degree.
`λ/d_eff`: `E < 0` mean `0.59`, `E ≥ 0` mean `0.81` — but the discriminant is `λ + S²/m` vs `d_eff`,
not `λ/d_eff` alone. Structurally `E < 0` = **the bottleneck regime** (a small set carries the spectral
mass): either dense-regular (`K_n` region) or a low-degree vertex bottleneck (TYPE A).

## TASK 4 — the hard-band lemma

`S_agg ≥ −E` (= `gap ≥ 0`) holds **29/29** in the `E < 0` band, tight (`= 1`) at `K_n`. This is the
conjecture restricted to regime ii — circular as a standalone, but now **localized**: regime ii =
`regular ∪ TYPE A`, each with its own (proven / extremality) route.

## The complete synthesis

| regime | `E` sign | family | tool | status |
|---|---|---|---|---|
| **i** (`Required ≤ 0`) | `E ≥ 0` | sparse, near-complete, TYPE B (lollipop) | **aggregate Poincaré** (`S_agg ≥ 0`) | `gap ≥ S_agg ≥ 0` (modulo aggregate) |
| **ii, regular** | `E < 0` | `K_n`, dense regular | **interlacing** `λ ≤ d+1` | **PROVEN** (`triEnergy_le_RHS_regular`) |
| **ii, TYPE A** | `E < 0` | deg2+dense, twin-port | **extremality** `gap/eff ≥ 1/3` | open (3 rigour items) |

> **The aggregate-slack dichotomy unifies the program:** `gap = S_agg − Required`. `Required ≤ 0`
> (regime i) ⟹ aggregate suffices; `Required > 0` (regime ii) splits into regular (proven) and TYPE A
> (extremality). This recovers the original 3-regime classification *exactly*, now with the
> `gap = S_agg + E` identity making the regime-i case a one-line consequence of the aggregate Poincaré.

## TASK 5 — does regular + TYPE A cover all `E < 0`?

**Yes, in the corpus:** every `E < 0` graph is regular (proven) or TYPE A (deg2+dense / twin-port,
low-degree vertex bottleneck → extremality). No `E < 0` graph fell outside. So:

> **Conjecture B reduces to: (i) aggregate Poincaré `T ≤ λd_eff` for `E ≥ 0` [regime i]; (ii) the TYPE A
> extremality bound `gap/eff ≥ 1/3` for irregular `E < 0` [regime ii], the regular `E < 0` being proven
> by interlacing.**

The two genuinely-open pieces are the **aggregate Poincaré** (regime i, the `aggregate_triangle_poincare`
sorry) and the **TYPE A extremality** (regime ii irregular). Everything else (regular `E < 0`, the
identity, regime-i reduction) is proven or a clean consequence.

## Conclusion

- **`E = −Required` exactly** — the aggregate-slack dichotomy *is* the regime split.
- **`E < 0` (regime ii) = `regular ∪ TYPE A`** (no residual); `E ≥ 0` (regime i) is dispatched by the
  aggregate Poincaré.
- **The complete reduction:** `gap ≥ 0 ⟸` [aggregate Poincaré (`E ≥ 0`)] ∧ [interlacing (regular
  `E < 0`, proven)] ∧ [TYPE A extremality (irregular `E < 0`)]. The synthesis unifies every prior round.

## Lean
`Required = −E` and `gap = S_agg − Required` are clean identities. The reduction: `E ≥ 0` →
`aggregate_triangle_poincare`; regular `E < 0` → `triEnergy_le_RHS_regular` (proven); irregular `E < 0`
→ the TYPE A extremality target. No single new lemma, but the dichotomy gives the cleanest case-split
for a future `triEnergy_le_RHS` proof.
