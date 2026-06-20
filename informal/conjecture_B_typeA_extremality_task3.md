# TYPE A extremality — TASK 3: adding `a~b` raises `gap/eff` at the extremizer

Compare the twin-port model with and without the port edge `a~b`. **Result (honest):** at the
extremizer `d=2` (and `d ≤ 6`), `a~b` *raises* `gap/eff`, so the minimizer keeps `a≁b`; for large `d`
(`≥8`) `a~b` *lowers* `gap/eff`, but those configs have `g ≫ 1/3` regardless, so the **global
minimizer `d=2, s=2, a≁b` is unaffected**. Code:
[`conjecture_B_typeA_extremality_task3.py`](../conjecture_B_typeA_extremality_task3.py).

## TASK 3a/3b — what `a~b` changes

The symmetric quotient row for `a` is **unchanged** by `a~b` (degree `+1` and the new neighbour value
`+p` cancel: `(d+1−λ)p = x + … ` becomes `(d+2−λ)p = x + … + p`), so **`λ₂` and the Fiedler `(x,p,c,r)`
are identical** with/without `a~b` (verified: `λ` columns coincide). The edge `a–b` itself has
`g_{ab} = (f_a−f_b)² = 0` (twins) so contributes nothing to `T` or `B2′` *directly* — but it raises
`deg(a), deg(b)` by 1, which **shifts the `min(d_a,d_b)−1` weights** on the `a`/`b`–port edges, so
`B2′` does change. Net effect on `gap`:

| `d` | `gap(a≁b)` | `gap(a~b)` | `gap(a~b)/gap(a≁b)` |
|---|---|---|---|
| 2 | 0.686 | 0.689 | **1.00** (unchanged) |
| 3 | 0.755 | 0.659 | 0.87 |
| 4 | 0.721 | 0.570 | 0.79 |

So `gap` is essentially unchanged at `d=2` and *decreases* for larger `d`. **`eff`, however, drops
cleanly:**

> **`eff(a~b) = 2/(d+2−λ)`** (the `a–b` edge raises the antisymmetric "degree" by 2), vs
> `eff(a≁b) = 2/(d−λ)`. Verified: `d=2` model `0.667 = 2/3`; ratio `eff(a≁b)/eff(a~b) = (d+2−λ)/(d−λ)`.

## TASK 3c — the extremizer (`d=2`)

`λ=1`: `eff(a≁b)=2`, `eff(a~b)=2/(4−1)=2/3` (ratio **3**); `gap` unchanged at `2/3`. Hence

> **`g(2,2,a≁b) = 1/3` → `g(2,2,a~b) ≈ 1`** (`= (2/3)/(2/3)`): adding `a~b` **triples** `gap/eff` at
> the extremizer (driven entirely by `eff` dropping 3×). Verified `N=400,800,1600`: `g(a~b) = 1.10,
> 1.05, 1.02 → 1`, vs `g(a≁b) → 1/3`.

So the minimizing configuration keeps **`a≁b`** — confirming the extremizer of `conjecture_B_typeA_twin_port_proof.md`.

## TASK 3d — general `d` (honest result)

`g(a~b)/g(a≁b) = [gap(a~b)/gap(a≁b)]·[eff(a≁b)/eff(a~b)]`. The eff-factor `(d+2−λ)/(d−λ) > 1` always,
but the gap-factor `< 1` and shrinking. The product:

| `d` | `g(a≁b)` | `g(a~b)` | `a~b` raises? |
|---|---|---|---|
| 2 | 0.34 | 1.04 | **yes** (×3) |
| 3 | 0.66 | 1.24 | yes |
| 4 | 0.93 | 1.31 | yes |
| 5 | 1.14 | 1.33 | yes |
| 6 | 1.29 | 1.33 | yes (marginal) |
| 8 | 1.51 | 1.31 | **no** |
| 12 | 1.74 | 1.29 | **no** |

> **The "`a~b` raises `g` for all `d`" claim is FALSE** — it fails for `d ≥ 8` (where the gap-drop
> overcomes the eff-drop). **But this does not affect extremality:** for `d ≥ 8`, *both* `g(a≁b)` and
> `g(a~b)` are `≥ 1.29 ≫ 1/3`, so neither is the global minimizer. The relevant statement —

> **at the global minimizer `d=2`, `a≁b` strictly beats `a~b` (`1/3 < 1`)** — holds, and that is all
> the extremality argument needs.

## Conclusion

- **At the extremizer (`d=2`):** `a~b` raises `gap/eff` from `1/3` to `≈1` (eff drops 3×, gap
  unchanged). So the minimizer is `a≁b` — confirmed.
- **Mechanism:** `λ₂` and Fiedler are `a~b`-invariant; `eff(a~b) = 2/(d+2−λ) < 2/(d−λ)` (clean,
  proven); `gap` is `≈` unchanged for small `d`, decreasing for large `d`.
- **Honest caveat:** `a~b` does *not* raise `g` for all `d` (fails `d ≥ 8`), but those configs are far
  from the minimum (`g ≫ 1/3`), so the **global minimizer `(d=2, s=2, a≁b)` stands**.

Monotonicity **(iii)** holds in the form that matters (at the extremizer / for the global minimum).
Combined with TASK 1 (`d=2` min over `d`) and TASK 2 (`s=d` min over `s`), the minimizer over all
port configs `(d, s, a~b)` on a complete bulk is **`d=2, s=2, a≁b`, `g = 1/3`**. Remaining: TASK 4
(complete bulk minimizes over bulk density — the rigidity step).

## Lean
The `a~b`-invariance of the quotient and `eff(a~b) = 2/(d+2−λ)` are clean equitable-partition facts.
The extremizer statement (`g(2,2,a≁b) = 1/3 < g(2,2,a~b)`) is the formalisable content; the "all-`d`"
version is false and not needed.
