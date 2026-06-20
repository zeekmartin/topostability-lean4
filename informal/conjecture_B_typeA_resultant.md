# Conjecture B — TYPE A regular core: resultant elimination (last algebraic attempt)

Goal: eliminate `λ` between the secular `P(λ,ρ,n)=0` and `Num(λ,ρ,n)` (from `gap = Num/Den`, `Den>0`)
to certify `Num(λ*) > 0` at the secular root for all valid `(ρ,n)`. Code:
[`conjecture_B_typeA_resultant.py`](../conjecture_B_typeA_resultant.py) (sympy).

**Caveat (decisive):** the *exact* secular for a general regular core is **not polynomial** (it needs
the full core spectrum). Only the **mean-field cubic** `P` is polynomial — and it is even
*qualitatively* wrong for the complete core (where the exact `λ=2` is not a root of `P_rest`). So any
resultant works on the η=0 *model* at the *mean-field* secular, exact only for the complete core.

## TASK 1 — `R = Res_λ(P, Num) ≡ 0` (trivially)

> `R = 0` identically, because `gcd(P, Num) = λ`: both vanish at the **null mode `λ = 0`** (the
> constant eigenvector), a shared root that has nothing to do with the Fiedler. The resultant is
> blind to *which* root is shared.

## TASK 1b/2 — reduced resultant on the bottleneck factor

Divide out the null mode: `P_rest = P/λ` (quadratic, roots the bottleneck `λ* ≈ 2` and a **spurious
high mode `λ_big ≈ ρ`**), `Num_rest = Num/λ`.

> `R_reduced = Res_λ(P_rest, Num_rest)` is a **degree-10** polynomial in `(ρ,n)`, **not** identically
> zero — but it is **sign-indefinite** over `3 ≤ ρ ≤ n−2`, `n ≥ 6` (`signs = {−1,+1}`), so it
> **vanishes somewhere in the valid range**.

## TASK 3 — which root is shared at the zeros?

At a sign-change of `R_reduced`, the shared root of `(P_rest, Num_rest)` is the **spurious `λ_big ≈ ρ`**,
never the bottleneck `λ*`:

> `Num(λ*) > 0` for **every** tested `(ρ,n)` (gap sign `+` throughout, values `10³–10⁶`). The
> bottleneck root is never a root of `Num`; the resultant's zeros come entirely from the high mode.

The resultant conflates `λ*` with `λ_big` and cannot separate them — `λ*` is irrational and not an
algebraic factor of `P_rest`. So `R_reduced ≠ 0` cannot be established (it *does* vanish, from `λ_big`),
and the elimination gives **no certificate** for `Num(λ*) > 0`.

## TASK 4 — Sturm count of `Num` in `[1,2]` (where `λ*` lives)

| ρ | n | λ* | #roots of Num in [1,2] | Num(λ*) | gap |
|---|---|---|---|---|---|
| 3 | 100 | 1.299 | **0** | 1.96e5 | + |
| 5 | 100 | 1.581 | **0** | 2.17e5 | + |
| 10 | 100 | 1.809 | **0** | 2.24e5 | + |
| 20 | 100 | 1.919 | 2 | 2.40e5 | + |
| 50 | 100 | 1.981 | 2 | 3.05e5 | + |
| 98 | 100 | 2.000 | 2 | 4.16e5 | + |

> **Small `ρ`: 0 roots of `Num` in `[1,2]`** ⇒ `Num > 0` throughout the interval ⇒ since `λ* ∈ [1,2]`,
> `gap > 0` is **proved by Sturm** (for the model). **Large `ρ`: 2 roots in `[1,2]`** clustered near
> `λ* ≈ 2` ⇒ `Num` is sign-indefinite there and an interval method **cannot isolate `λ*`** from the
> nearby roots (a sharper bracket `[λ*−ε, λ*+ε]` would need `λ*` located, which is irrational).

So Sturm closes the *sparse* end and fails exactly in the *dense* genuine-TYPE-A end.

## Conclusion — algebraic elimination cannot close general TYPE A

1. **No polynomial exact secular.** The exact `λ` for a general regular core depends on the full core
   spectrum; only the mean-field `P` is polynomial, and it is wrong for the complete core. Resultant
   methods therefore analyse the *model*, not the true gap.
2. **Trivial + spurious shared roots.** `Res(P,Num) ≡ 0` from the null mode `λ=0`; the reduced
   resultant vanishes from the spurious high mode `λ_big ≈ ρ`. The bottleneck `λ*` is never separated.
3. **`Num` sign-indefinite near `λ*` for large `ρ`** (Sturm = 2): no interval certificate.

This was the last algebraic attempt; it **fails** for the same root cause as the Schur, driver, and
polynomial analyses: `gap` is the `O(1/n)` residual at an irrational secular root that cannot be
algebraically isolated. **The clean result stands: the complete core `gap = 10(n−3)/m > 0`** (exact
`λ=2`, sympy-proven). General regular TYPE A remains reduced to the (universally verified, but not
algebraically certifiable) statement *"the secular root lands in the positive lobe of `Num`"*.

Partial wins along the way: complete-core closed form (proved), TYPE B fully closed (Lean), and the
sparse-`ρ` end provable by Sturm.

## Lean
No new lemma (symbolic/numeric negative result). The standing positive Lean/closed-form content:
TYPE B (`typeB_triEnergy_bound`, sorry-free) and the complete-core `gap = 10(n−3)/m`.
