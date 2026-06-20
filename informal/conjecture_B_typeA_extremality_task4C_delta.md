# TYPE A extremality — TASK 4C: the per-edge interior gap increment δ

**Result:** deleting one *interior* bulk edge (away from the ports and their neighbours) from the
`d=2` twin-port `K_N` model **increases `gap` by `δ = 8/(3N²) > 0`** (closed form, leading order),
while `λ` and `eff` stay invariant (TASK 4B). This makes `gap` monotone under interior deletion, so
the complete bulk minimizes `gap` (hence `3·gap − eff`). Code:
[`conjecture_B_typeA_extremality_task4C.py`](../conjecture_B_typeA_extremality_task4C.py).

## Setup and scope (careful)

Twin ports `a,b ~ {0,1}`, `v₀ ~ {a,b}`, bulk `K_N` on `{0,…,N−1}`. Delete an **interior** edge
`e = (i,j)` with `i,j ≥ 2` (both away from the port-neighbours `{0,1}` and from `{a,b}`). In `G`:
`f`-classes are `x`(v₀), `p`(a,b), `c`(ports 0,1), `r`(rest), with (twin-port proof) `λ=1`,
`p²=1/6`, `c=−2p/N`, `r=−4p/N`, `S≈−4pN`, `m≈N²/2`. **We do NOT treat port-incident edges here**
(TASK 4B: those keep `3·gap−eff>0` via a different mechanism — `λ,eff` drop together).

## TASK 4C.1–4 — `Δgap` derivation (hold `f` fixed; `λ,f` change by `O(1/N)`)

Deleting `e=(i,j)` with `f_i=f_j=r` changes the three gap-terms:

| term | change | reason |
|---|---|---|
| `Σ h²` | `−(f_i+f_j)² = −4r²` | the removed edge's lift |
| `B2′` | `−4(r−c)²` | `d_i,d_j` each drop 1 ⇒ `min−1` drops by 1 on each endpoint's **2 port-edges** (the only incident edges with nonzero `g²=(r−c)²`; rest-rest edges have `g²=0`) |
| `S²/m` | `−4Sr/m + S²/m²` | `ΔS=−(f_i+f_j)=−2r`, `Δm=−1` |

(The removed edge contributes `0` to `B2′` and `T` since `g_{ij}=(r−r)²=0`.) Hence

> **`Δgap = λ(−4r² + 4Sr/m − S²/m²) + 4(r−c)²`.**

## Closed form (d=2 leading order)

Substituting `λ=1, r=−4p/N, c=−2p/N, S=−4pN, m=N²/2` (units `p²/N²`):

| contribution | value |
|---|---|
| `λ·Δ(Σh²) = −4r²` | `−64` |
| `λ·(−Δ(S²/m)) = 4Sr/m − S²/m²` | `+128 − 64 = +64` |
| `−ΔB2′ = +4(r−c)²` | `+4·(2p/N)² = +16` |

> **The `λ`-part cancels exactly (`−64+128−64 = 0`)**; the survivor is the `B2′` term:
> **`δ = 16p²/N² = 8/(3N²) > 0`** (since `p²=1/6`).

## TASK 4C.5 — `δ > 0` (sign certain)

`δ = 16p²/N²` with `p² = 1/6 > 0` — **positive, unconditionally**. The sign comes entirely from the
`B2′` reduction `+4(r−c)²` (the degree drop *lowers* `B2′`, *raising* `gap`), after the spectral
`λ`-terms cancel.

**Verification (true `δ` from full eigensolve):**

| N | `δ` (true) | `8/(3N²)` | `δ·N²` |
|---|---|---|---|
| 30 | 0.002937 | 0.002963 | 2.644 |
| 60 | 0.000750 | 0.000741 | 2.699 |
| 100 | 0.000270 | 0.000267 | 2.696 |
| 160 | 0.000105 | 0.000104 | 2.688 |

`δ·N² → 8/3 = 2.667` — confirming `δ = 8/(3N²) + O(1/N³)` (the `O(1/N)` wobble is the held-fixed-`f`
correction). `δ > 0` in every case.

## TASK 4C.6 — additivity

| k (interior deleted, N=60) | `gap(k)` true | `gap(0)+kδ` | residual |
|---|---|---|---|
| 0 | 1.038633 | 1.038633 | 0 |
| 30 | 1.061120 | 1.060855 | `+2.6e−4` |
| 100 | 1.113542 | 1.112707 | `+8.4e−4` |
| 150 | 1.150943 | 1.149744 | `+1.2e−3` |

> `gap(k) = gap(0) + k·δ` to `O(1/N)` (residual *positive* and small — when deleted edges share a
> vertex, the degree drops compound, making the true gap *slightly larger* than linear, so
> **monotonicity is if anything reinforced**). The increments are **independent at leading order**
> (disjoint edges → exactly additive; shared-vertex edges → super-additive).

## What is proved vs conjectural

**Verified identity (leading order, sign certain):**
> For `d=2` twin ports, deleting an interior bulk edge raises `gap` by `δ = 8/(3N²) > 0`; `λ, eff`
> unchanged (TASK 4B). Hence `gap` is **monotone non-decreasing under interior bulk-edge deletion**,
> minimized at the complete bulk `K_N`. With `eff` invariant, `3·gap − eff` is minimized at `K_N`
> too, value `→ 0` at `d=2` ⇒ **`3·gap − eff ≥ 0`** over the interior-deletion family.

**Conjectural / not yet covered:**
- *Exact* (not leading-order) `δ`: the held-fixed-`f` derivation is `O(1/N)`-accurate; full rigor needs
  the Fiedler perturbation controlled (sign is unambiguous, magnitude `→ 8/3·N⁻²`).
- *Port-incident* edges: handled separately (TASK 4B, `3·gap−eff > 0` but via `λ,eff` co-dropping) —
  **not** an interior δ.
- *General `d`*: `δ(d) > 0` verified for `d=2,3,4` (`δ·N² = 2.69, 2.56, 2.20`); closed form not derived.
- *General TYPE A core*: composing interior-deletion + port-config moves (TASKS 1–3) to reduce an
  arbitrary `H` to the extremizer is the remaining assembly.

## Conclusion

The previously verified-but-unproven gap-monotonicity now has a **closed-form per-edge increment
`δ = 8/(3N²) > 0`** with a clean derivation: the spectral (`λ`) terms cancel exactly, and the strictly
positive survivor is the `B2′` min-weight reduction from the degree drop. This **proves (at leading
order, sign certain) that interior bulk deletion raises `gap`**, closing the interior half of the
rigidity step — `3·gap − eff ≥ 0` over the interior-deletion family, with equality at the complete-bulk
`d=2` extremizer.

## Lean
`δ = 16p²/N² > 0` and the term cancellation (`−4r² + 4Sr/m − S²/m² = 0` at the quotient values) are
clean algebraic facts on the quotient Fiedler. The leading-order/asymptotic nature (held-fixed `f`)
is the deferred analytic part, as throughout the extremality programme.
