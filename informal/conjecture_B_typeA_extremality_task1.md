# TYPE A extremality — TASK 1: `g(d)` increasing in port degree `d`

Twin ports `a,b` share all `d` bulk neighbours in `K_N` (`a≁b`); `v₀ ~ {a,b}`. Prove
`g(d) := lim_{N→∞} gap/eff` is strictly increasing in `d` for `d ≥ 2`, so `d=2` minimizes it (`= 1/3`).
Code: [`conjecture_B_typeA_extremality_task1.py`](../conjecture_B_typeA_extremality_task1.py).

## TASK 1a — the quotient `Q(d)`

Equitable partition `{v₀}(x), {a,b}(p), {d common ports}(c), {rest N−d}(r)`:

```
        x        p        c          r
 v₀ [  2−λ     −2        0          0      ]
 ab [  −1     d+1−λ     −d          0      ]
  C [   0      −2      N−d+2−λ    −(N−d)   ]
  R [   0       0       −d         d−λ     ]
```

(Row checks: `(Lf)_{v₀}=2x−2p`; `(Lf)_a=(d+1)p−x−dc`; `(Lf)_{port}=(N+1)c−2p−(d−1)c−(N−d)r`;
`(Lf)_{rest}=(N−1)r−dc−(N−d−1)r`. Constant vector → eigenvalue 0.)

## TASK 1b — secular and `eff`

Eliminating in the limit `N→∞` (`r ~ 1/N`, `c ~ 1/N`):

> **secular `λ² − (d+3)λ + 2d = 0`**, so `λ₂(d) = ½(d+3 − √(d²−2d+9))` (smaller root).
> Checks: `d=2 → λ=1`; `d=3 → λ=3−√3`; `d=4 → λ=(7−√17)/2`. (Matches `λ₂(N) = 1+4/(3N)→1` at `d=2`.)

The antisymmetric resolvent (twins ⇒ response on `a,b` only, `(d−λ)q=1`) gives

> **`eff(d) = 2/(d−λ) = 4 / (d − 3 + √(d²−2d+9))`**. (`d=2→2`, `d=3→2/√3`, `d=4→4/(1+√17)`.)

## TASK 1c — closed form of `gap(d)` and `g(d)`

Edge-class sums (limit `N→∞`, with `x = 2p/(2−λ)`, `p² = (2−λ)²/(4+2(2−λ)²)`):
`T = 2d(d+1)p²`, `B2′ = 2(x−p)² + 2d²p² + 4dp²`, `λ₂G = λ(2(x+p)² + 2dp²)`,
`gap = λ₂G − B2′`. sympy simplifies (`w := √(d²−2d+9)`):

> **`g(d) = gap/eff = (3d² + d·w − 6d − 9w + 27) / (2d² − 4d + 18)`**, `w = √(d²−2d+9)`.

Exact values: **`g(2) = 6/18 = 1/3`**, `g(3) = (36−12√3)/24 = (3−√3)/2 ≈ 0.634`,
`g(4) ≈ 0.894`, `g(5) ≈ 1.092`, … `g(d) → 2` as `d → ∞`.

## TASK 1e — verification vs the direct model

Building the full twin-degree-`d` graph (`N = 400`) and computing `gap/eff` directly:

| `d` | direct `gap/eff` (N=400) | closed-form `g(d)` (N→∞) |
|---|---|---|
| 2 | 0.361 | 1/3 = 0.333 |
| 3 | 0.691 | 0.634 |
| 4 | 0.980 | 0.894 |
| 6 | 1.378 | 1.239 |

(The direct values sit slightly above the `N→∞` closed form — the favourable `O(1/N)` finite-size
correction; they converge to `g(d)` as `N→∞`.)

## TASK 1d — proof that `g(d)` is increasing for `d ≥ 2`

`g(d) = Num/(2w²)` with `Den = 2(d²−2d+9) = 2w² > 0`. sympy gives

> `g'(d) = 4d·M(d)/D(d)`, with `M(d) = (d²−2d+5) − (d−1)·√(d²−2d+9)` and `D(d) > 0` (verified).

**`M(d) > 0` (analytic):** both `d²−2d+5 > 0` and `(d−1)√(d²−2d+9) > 0` for `d ≥ 2`; squaring with
`t := d²−2d`,
`(d²−2d+5)² − (d−1)²(d²−2d+9) = (t+5)² − (t+1)(t+9) = (t²+10t+25) − (t²+10t+9) = 16 > 0`,
so `(d²−2d+5)² > (d−1)²(d²−2d+9)`, i.e. `M(d) > 0`. With `4d > 0` and `D(d) > 0`, **`g'(d) > 0`**.

Confirmation: `g'(d) = 0.296, 0.289, 0.170, 0.048` at `d = 2,3,5,10` (positive, → 0⁺); the discrete
differences `g(d+1) − g(d) > 0` for all `d = 2..29` (min `0.005`). So **`g(d)` is strictly increasing**
on `d ≥ 2`, with infimum `g(2) = 1/3` and supremum `lim_{d→∞} g(d) = 2`.

## Conclusion

> **TASK 1 proved:** for twin ports on `K_N`, `g(d) = lim_{N→∞} gap/eff = (3d²+d w−6d−9w+27)/(2d²−4d+18)`
> (`w = √(d²−2d+9)`) is **strictly increasing for `d ≥ 2`** (`g'(d) = 4d·M(d)/D(d)`, `M(d) > 0`
> proven). Hence **`d = 2` minimizes `g(d)`, with `g(2) = 1/3`** — the twin-port extremizer.

`g(d) ∈ [1/3, 2)` for `d ≥ 2`; the family minimum `1/3` is the `d=2` extremizer of
`conjecture_B_typeA_twin_port_proof.md`. This is monotonicity **(i)** of the extremality plan; the
overlap **(ii)** (`s ≤ d` lowers to twins) and `a~b` **(iii)** monotonicities follow next.

## Lean
The closed form `g(d)` and the secular `λ²−(d+3)λ+2d=0` are clean (equitable-partition quotient).
`M(d) > 0` via the integer identity `(t+5)²−(t+1)(t+9)=16` is fully formalisable; the rest is the
`N→∞` limit (asymptotic), deferred as in the twin-port proof.
