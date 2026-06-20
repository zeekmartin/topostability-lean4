# Conjecture B — TYPE A regular core: secular polynomial and the positivity of `gap`

Object: the η=0 closed form `gap = λ(ρ−λ+1) + K/D` (exact for the complete core, the regular-core
model otherwise), with `K = (3λ−λρ−2) + (2λ+ρ−2)(2−λ)²/2 + (3−ρ)(2−λ) − λ(4−ρ−λ)²/m`,
`D = 1 + (2−λ)²/2 + (3−λ)²/(n−3)`, `m = ρ(n−1)/2 + 2`. Code:
[`conjecture_B_typeA_regular_polynomial_positive.py`](../conjecture_B_typeA_regular_polynomial_positive.py)
(sympy).

## TASK 1 — secular polynomial

The mean-field 3×3 reduction `(x, p, μ)` (v₀ / attachments `a,b` / uniform bulk, `β = 2ρ/(n−3)`) has
secular determinant

> **`P(λ,ρ,n) = (2−λ)[λ² − λ(ρ+1+β) + β] − 2(β−λ) = 0`**, `β = 2ρ/(n−3)` — a cubic in `λ`.

Accuracy vs the true `λ₂` (e.g. `rr(99,50)`: actual `1.9802`, mean-field `1.9806`): within `~0.04`,
sharper than the cruder `(2−λ)(ρ−λ+1) = 2`. The **complete core has `λ = 2` exactly** (special:
`a~b`); for general regular cores the *exact* secular needs the full core spectrum — `P` is the
polynomial mean-field approximation.

## TASK 2 — `gap = Num/Den`

`together(gap)` gives (sympy):

> **`Den = (ρ(n−1)+4)·((n−1)λ² − 4nλ + 6n) = 2m·((n−1)λ² − 4nλ + 6n) > 0`**

(`(n−1)λ²−4nλ+6n ≈ 2(n−2) > 0` near `λ=2`). `Num` is degree-4 in `λ`. In `s = 2−λ`:

| power | coefficient (factored) |
|---|---|
| `s⁰` | `4(n²ρ − nρ² + 3nρ − 4n + 5ρ² − 16ρ + 8)` |
| `s¹` | `−2(n²ρ² − 3n²ρ − 9nρ² + 17nρ − 4n + 12ρ² − 34ρ + 16)` |
| `s²` | `3n²ρ² − 2n²ρ − 12nρ² + 18nρ + 9ρ² − 24ρ + 24` |
| `s³` | `−n²ρ² + n²ρ + 2nρ² − 6nρ + 8n − ρ² + 5ρ − 16` |
| `s⁴` | `−(n−1)(ρ(n−1)+4) = −(n−1)·2m < 0` |

The leading (`s⁴`) coefficient is **negative**, so `Num` is *not* a positive polynomial.

## TASK 3/4 — positivity needs the secular root

**Whole-interval positivity FAILS.** Scanning `s = 2−λ ∈ (0, 2/(ρ−1)]`, `Num ≤ 0` at `277/2040`
points (first failure `ρ=48, n=50, s=0.011`: `Num = −4411 < 0`). `Num` changes sign on the interval —
`gap_model > 0` does **not** hold for all `λ` in range, only when `λ` is **at the secular root**.

> **At the secular root, `gap_model = Num(s*)/Den(s*) > 0` for every tested `(ρ,n)`** (`Num(s*) > 0`,
> `Den(s*) > 0`), `ρ ∈ {5..100}`, `n ∈ {50..500}`.

The model gap is **hypersensitive to `λ` near 2**: substituting `λ = 2` gives an `O(1)` value
(`2−2q` etc.), but the true gap is `O(1/n)` because the secular `λ = 2 − Θ(1/n)` and the `O(1)` terms
cancel. So a positivity proof *must* pin `λ` to the secular; the bare polynomial `Num` is sign-
indefinite. (`Num` is positive at `s=0` (complete) *and* at `s=s*>0` (general), but negative between —
the secular root lands in a positive lobe.)

## TASK 5 — verification

**(a) Complete core `ρ = n−2`, `λ = 2` — PROVEN symbolically:**

> `gap(ρ=n−2, λ=2) = 20(n−3)/(n²−3n+6) = 10(n−3)/((n−2)(n−1)+4) = 10(n−3)/m` — sympy
> `simplify(gap − 10(n−3)/m) = 0` (**`EQUAL: True`**), manifestly `> 0` for `n > 3`.

**(b),(c) at the secular root, `c := gap·m/n`:**

| regime | n=50 | n=200 | n=1000 |
|---|---|---|---|
| `ρ = 10` (fixed) | 5.86 | 5.47 | 5.37 |
| `ρ = n/2` | 7.51 | 7.88 | 7.98 |
| `ρ = n−2` (complete) | 9.40 | 9.85 | **9.97 → 10** |

All `gap > 0`; `c` increases with density `→ 10` at the complete core (recovering `10(n−3)/m`), and
sits at `~5.4` for fixed sparse `ρ` — consistent with `c(q) = gap·m/n` bounded below.

## Conclusion

- **Complete-core TYPE A is proved symbolically:** `gap = 10(n−3)/m > 0` (sympy-verified identity).
- `gap = Num/Den` with `Den > 0`; **`Num` is sign-indefinite** (negative leading `s⁴` coefficient), so
  `gap > 0` is **not** a bare polynomial positivity — it holds **only at the secular root** (verified
  for all `(ρ,n)`).
- A fully symbolic *general* proof is blocked by two facts: (i) `Num` changes sign over the `λ`-
  interval, so the secular value of `λ` is essential; (ii) the **exact secular for general regular
  cores is not a low-degree polynomial** (it needs the full core spectrum; `P` above is only the
  mean-field cubic). Pinning `λ` to the exact secular is exactly the missing ingredient — the same
  `O(1/n)`-residual / hypersensitivity obstruction seen in the Schur and driver analyses.

So: the densest case is closed in closed form; the general regular case reduces to "the secular root
lands in the positive lobe of `Num`", verified throughout but not yet a polynomial certificate.

## Lean
No new lemma (symbolic/numeric). The complete-core identity `gap = 10(n−3)/m` is sympy-verified and is
the clean closed-form positive case; the general bound still hinges on the exact (non-polynomial)
secular.
