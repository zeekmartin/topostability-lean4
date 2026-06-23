# Conjecture B — the minimal TYPE A sorry `typeA_slack_ge_required`

Focus on the single remaining TYPE A sorry `typeA_slack_ge_required : required ≤ aggregateSlack`.
**Result: it is exactly the lift bound `triEnergy ≤ RHS` in regime ii (irreducible as an abstract
scalar). It cannot be closed without the full TYPE A extremality program (too large), but it is
SHARPENED: via the new sorry-free `triEnergy_le_of_partition`, it reduces to the scalar condition
`maxt_port·D_port + maxt_core·D_core ≤ RHS` (with the TIGHT lift RHS), validated 19/19 on regime-ii
TYPE A (max ratio 0.935) — a single block-flatness inequality, strictly sharper than the aggregate
bound.** Code: [`aggregate_typeA_lean_bridge.py`](../aggregate_typeA_lean_bridge.py).

## TASK 1 — exact Lean definitions

```
triEnergy G f      = Σ_i Σ_j [G.Adj i j] |N_i ∩ N_j| · (f_i − f_j)²     (ordered)
degQuad G f        = Σ_v d_v · f_v²
degLin  G f        = Σ_v d_v · f_v                         -- S
gapEnergy G f λ mE = 2λ·(2·degQuad − λ − degLin²/mE) − triEnergy        -- = RHS − triEnergy
aggregateSlack G f λ = 2λ·degQuad − triEnergy
required G f λ mE  = 2λ·(λ + degLin²/mE − degQuad)         -- = −E ; > 0 in regime ii
```
`λ` is the Laplacian eigenvalue (`L_G f = λf`); `mE = |E|`.

## TASK 2 — scalar translation

`required ≤ aggregateSlack`
`⟺ 2λ(λ + S²/mE − degQuad) ≤ 2λ·degQuad − triEnergy`
`⟺ triEnergy ≤ 2λ·(2·degQuad − λ − S²/mE) = RHS` (`⟺ gapEnergy ≥ 0`).

> **`typeA_slack_ge_required` is exactly the lift bound `triEnergy ≤ RHS` in regime ii** — the conjecture
> content, irreducible as an abstract scalar. The aggregate Poincaré only gives `triEnergy ≤ 2λ·degQuad`,
> which is **looser than RHS in regime ii** (`RHS < 2λ·degQuad ⟺ required > 0`), so it does not suffice.

## TASK 3 — the informal TYPE A extremality program (what would close it)

`triEnergy ≤ RHS` in regime ii is the TYPE A extremality `gap/eff ≥ 1/3`
(`informal/conjecture_B_hard_band_E_negative.md`, `aggregate_typeA_bottleneck.md`). Its ingredients —
twin-port `K_N` `d=2` extremizer (`gap/eff = 1/3`), `g(d)` increasing, overlap monotonicity, adding `a∼b`
invariance, interior-deletion `3·gap − eff` monotonicity, `δ_exact > 0` — are **only in informal notes**,
not Lean. Formalising them (define `eff`, the closed forms, four monotonicities, three rigour items) is a
large separate effort, far beyond reducing one sorry.

## TASK 4 — the sharper scalar reduction (implemented as `triEnergy_le_of_partition`)

The port/core machinery (`triEnergy_split`, `triEnergyOn_le`) gives, for any per-class triangle-count
bounds `Cp` (ports), `Cc` (core) and any target `B`:

> **`triEnergy_le_of_partition` (no `sorry`):** `Cp·D_port + Cc·D_core ≤ B  ⟹  triEnergy ≤ B`.

Taking `B = RHS` and the **exact** per-class maxima `Cp = maxt_port`, `Cc = maxt_core` (`t_e ≤ maxt`
trivially), `typeA_slack_ge_required` reduces to the single scalar inequality

> **`maxt_port·D_port + maxt_core·D_core ≤ RHS`** (the SHARP condition).

Validated on regime-ii TYPE A:

| family | bound/RHS |
|---|---|
| deg2+dense(80,.85) | 0.935 (worst) |
| deg2+dense(80,.6) | 0.830 |
| deg2+dense(80,.3) | 0.316 |
| twin-port `K₈₀` d2 | 0.510 |

> **19/19, max ratio 0.935** (margin ≥ 0.065). This is strictly sharper than the aggregate bound (`≤ 2λ·
> degQuad`, ratio up to 1 in regime ii) and uses the **tight RHS**. It is a *block-flatness* inequality:
> `D_core` is small (flat core), `D_port` carries the bottleneck; `maxt_core·D_core` is controlled by the
> core gap `γ > λ` and `RHS ≥ 2λ·portMass`.

The Δ_H (max core degree) version `(δ−1)D_port + Δ_H·D_core ≤ RHS` is **too lossy** (fails 2/17, up to
1.10) — the *exact* `maxt_core` is needed, not the degree bound.

## TASK 5 — status

- **`typeA_slack_ge_required` is NOT closed** (it is the regime-ii lift bound = TYPE A extremality;
  closing needs the large extremality program).
- **It is SHARPENED:** `triEnergy_le_of_partition` (new, sorry-free) reduces it to the single validated
  scalar `maxt_port·D_port + maxt_core·D_core ≤ RHS` (19/19, max 0.935) — a block-flatness inequality
  against the tight RHS, strictly sharper than the aggregate bound.
- **Lean:** sorry count unchanged at 3 (`aggregate_triangle_poincare` 854, `typeA_slack_ge_required` 994,
  `conjectureB` 1077); `triEnergy_le_of_partition` added sorry-free (generalizes
  `aggregate_triangle_poincare_typeA` to an arbitrary bound `B`, in particular `RHS`).
  `aggregate_triangle_poincare` and `conjectureB` untouched.

## Conclusion

`typeA_slack_ge_required` is the irreducible regime-ii lift bound; it cannot be made a *smaller abstract*
sorry. The sorry-free `triEnergy_le_of_partition` provides the SHARPER route: reduce it to the single
scalar `maxt_port·D_port + maxt_core·D_core ≤ RHS` (validated 19/19), whose proof is the block-flatness
+ port-mass content (`poincare_on_block`, future work). The remaining gap is exactly the TYPE A
extremality, now expressed against the tight RHS.
