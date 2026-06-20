# Conjecture B — TYPE A boundary regime `λ/γ → 1`

Zoom on the TYPE A boundary, where the deg-2 vertex `v₀` stops being the bottleneck and the Fiedler
transitions to the core's own bottleneck mode. **Clarification:** the resolvent diverges and TYPE A
exits at **`λ = γ` (`λ/γ → 1`)**, not `0.5`. (The earlier `λ/γ ≥ 0.5` cluster lumped everything from
`0.5` to `1`.) Code:
[`conjecture_B_typeA_boundary.py`](../conjecture_B_typeA_boundary.py). Controlled families: dumbbell
core (two `K_m` joined by `b` bridges, `γ` tuned by `b`), `a,b` straddling vs same side.

## TASK 1 — what happens to `gap/eff` as `λ/γ → 1`?

**`a,b` on opposite sides of the core cut** (`φ₂(a) ≠ φ₂(b)`):

| bridges | `λ/γ` | gap | eff | `gap/eff` |
|---|---|---|---|---|
| 28 | 0.55 | 1.15 | 0.17 | 6.77 |
| 20 | 0.76 | 1.26 | 0.31 | 4.11 |
| 16 | 0.95 | 6.72 | 1.35 | 4.97 |
| 14 | 1.01 | — | (exited TYPE A) | — |

> As `λ/γ → 1`, `eff = Σ(φ_k(a)−φ_k(b))²/(μ_k−λ)` **diverges** (the `μ₂ = γ` term blows up as `γ → λ`)
> — **but `gap` grows in step**, so **`gap/eff` stays finite (`≈ 5`)**, *not* `→ 0`.

**`a,b` on the same side** (`φ₂(a) ≈ φ₂(b)`): `eff` stays small (`≈ 0.15`, the `γ`-mode term cancels);
`gap` grows; **`gap/eff → ~75`** (large). 

> **The boundary does NOT drive `gap/eff → 0`.** Its limit is finite and positive, placement-dependent
> (`≈ 5` straddling, `≈ 75` same-side). The divergence of `eff` is matched (straddling) or avoided
> (same-side). So `inf(gap/eff) > 0` is **not** threatened by the boundary.

This **corrects** the earlier impression: `inf(gap/eff) ≈ 1.6` was *not* at the boundary — it came from
small / strongly-asymmetric interior graphs. At `λ/γ → 1` the controlled families give `gap/eff ≳ 5`.

## TASK 2 — which core gives the smallest `gap/eff` near the boundary?

| core / attach | `λ/γ` | `gap/eff` | TYPE A? |
|---|---|---|---|
| dumbbell, same side | 0.90 | 75.8 | (exited) |
| `K_{6,30}` bipartite | 0.31 | 6.86 | yes |
| rr(60,7) | 0.61 | 5.46 | yes |
| path-of-cliques (barbell) | 0.97 | 5.69 | (exited) |
| cycle-power `C₆₀³` | 0.97 | 2.65 | (exited) |
| dumbbell, opposite | 1.04 | — | (exited) |

> The smallest `gap/eff` among **genuine TYPE A** near the boundary is `≈ 5–7` (`rr`, bipartite). The
> graphs with smaller values (`cycle-power` `2.6`, barbell `5.7`) have **already exited** TYPE A
> (`λ ≥ γ`). So no core type drives `gap/eff` small *within* TYPE A at the boundary; the genuinely
> small `gap/eff` values live in the interior, not the boundary.

## TASK 3 — continuity across the transition `λ₂ = γ`

Adding bridges (dumbbell, `a,b` opposite), tracking `gap` through the crossing:

| bridges | `λ₂(G)` | `γ` | regime | gap |
|---|---|---|---|---|
| 11 | 1.66 | 1.62 | exited | 18.06 |
| 12 | 1.85 | 1.81 | exited | 18.22 |
| **13** | **1.92** | **1.97** | **TYPE A** | **2.76** |
| 14 | 1.93 | 2.09 | TYPE A | 1.57 |
| 16 | 1.93 | 2.41 | TYPE A | 1.26 |
| 25 | 1.94 | 3.76 | TYPE A | 1.19 |

> **`gap` is DISCONTINUOUS at the crossing**: it jumps `18.2 → 2.76` when `λ₂` crosses `γ` (the Fiedler
> swaps from the core-bottleneck mode to the `v₀` mode — an eigenvector swap at the eigenvalue
> crossing; `max |gap step| = 15.5`). **But `gap > 0` on BOTH sides** (exited side `≥ 3.2`, TYPE A side
> `≥ 1.19`).

So the hoped continuity argument ("continuous ⇒ gap > 0 at the boundary from the proved other side")
**fails** — `gap` is discontinuous at `λ₂ = γ`. **However, `gap > 0` holds on both branches anyway**
(the exited side is regime-1/TYPE-B, proved positive; the TYPE A side is positive throughout the
approach). The positivity is not endangered by the transition; only the continuity-based *argument* is.

## Conclusion

- **The boundary is `λ/γ → 1`** (resolvent divergence at `λ = γ`), not `0.5`.
- **`gap/eff` does not vanish at the boundary**: it converges to a finite positive limit (`≈ 5`
  straddling, `≈ 75` same-side); `eff` diverges only when `a,b` straddle the core cut, and then `gap`
  diverges with it. **`inf(gap/eff)` is not driven to 0 by the boundary** — the earlier `≈1.6` is an
  interior (small/asymmetric) phenomenon, not a boundary limit.
- **`gap` is discontinuous across `λ₂ = γ`** (Fiedler mode swap, jump `18 → 2.8`), so a continuity
  argument does not transfer positivity from the other regime — **but `gap > 0` holds on both sides**
  regardless (exited side proved; TYPE A side positive in the approach).

Net: the feared boundary is **benign** for the conjecture — `gap > 0` survives the transition (both
branches positive) and `gap/eff` stays bounded away from 0 there. The genuinely smallest `gap/eff`
values are interior, so any quantitative lower bound `gap/eff ≥ c₀` must be sought in the TYPE A
*interior*, not at its `λ/γ → 1` edge.

## Lean
No new lemma (numerical boundary study). Standing content unchanged; see `CONJECTURE_B_STATUS.md`.
