# Conjecture B — proof that `gap → 2/3` for the d=2 twin-port extremizer

The TYPE A extremizer: bulk `K_N`; two **twin ports** `a,b` each adjacent to the same two bulk
vertices `{0,1}` (`a ≁ b`); `v₀ ~ {a,b}`. Total `N+3` vertices. We compute the gap exactly via the
4-class equitable quotient and prove **`gap → 2/3`** (`N → ∞`), giving `gap/eff → 1/3`. Code:
[`conjecture_B_typeA_twin_port_proof.py`](../conjecture_B_typeA_twin_port_proof.py) (quotient = direct
to machine precision; symbolic limits via sympy).

## TASK 1 — the 4×4 quotient

Equitable partition: `V = {v₀}` (value `x`), `P = {a,b}` (`p`), `C = {0,1}` (`c`, the two common
ports), `R = {2..N−1}` (`r`, the `N−2` remaining bulk). Class-constant eigenvectors satisfy the
(non-symmetric) quotient Laplacian `L_Q v = λ v`:

```
[ 2−λ   −2     0       0     ] [x]
[ −1    3−λ   −2       0     ] [p]   = 0
[  0    −2    N−λ   −(N−2)   ] [c]
[  0     0    −2     2−λ     ] [r]
```

Row-by-row this is the exact `(Lf)_u = λ f_u`: `(2−λ)x = 2p` (v₀); `(3−λ)p = x+2c` (a,b, degree 3);
`(N−λ)c = 2p+(N−2)r` (ports, degree `N+1`); `(2−λ)r = 2c` (remaining, degree `N−1`). The kernel is the
constant vector (eigenvalue 0). Eliminating gives the secular `λ = (2−λ)²` in the `N→∞` limit, i.e.
`(λ−1)(λ−4)=0`; at finite `N`,

> **`λ₂(N) = 1 + 4/(3N) + O(1/N²) → 1`** (verified: `λ₂ = 1.001333` at `N=1000` vs `1+4/3000 =
> 1.001333`).

**Quotient Fiedler** (leading order): `x = 2p`, `c = −2p/N`, `r = −4p/N`, with normalization
`x²+2p²+2c²+(N−2)r² = 1 → 6p² = 1`, so

> **`p = 1/√6`, `x = 2/√6`, `c → −2/(√6·N)`, `r → −4/(√6·N)`.**

## TASK 2 — lift to the full graph and compute `gap`

The quotient gap **equals the direct full-graph gap** to machine precision (verified `N ≤ 300`), so
the class-constant Fiedler is exact. Summing over edge classes (only `g_e ≠ 0` edges contribute):

| edges | count | `t_e` | `min−1` | `g = (f_i−f_j)²` |
|---|---|---|---|---|
| `v₀–a, v₀–b` | 2 | 0 | 1 | `(x−p)²` |
| `a/b–port` | 4 | 1 | 2 | `(p−c)²` |
| `port–rest` | `2(N−2)` | `N−2` | `N−2` | `(c−r)²` |
| `port–port`, `rest–rest` | — | — | — | `0` |

- `T = 4(p−c)² + 2(N−2)²(c−r)²`. With `p−c → p`, `(c−r)² = 4p²/N²`: `T → 4p² + 8p² = 12p² = 2`.
- `B2′ = 2(x−p)² + 8(p−c)² + 2(N−2)²(c−r)²`. With `x−p = p`: `B2′ → 2p²+8p²+8p² = 18p² = 3`.
- `Σh² → 54p² = 9`; `S = 2x+6p+2(N+1)c+(N−1)(N−2)r ≈ −4pN`, so `S²/m → 32p² = 16/3`;
  `λ₂G = λ·(Σh²−S²/m) → 1·(54−32)p² = 22p² = 11/3`.

> **`gap = λ₂G − B2′ → 22p² − 18p² = 4p² = 4/6 = 2/3`.**

Verified symbolically (sympy `limit`, `N→∞`): `T → 2`, `B2′ → 3`, `Σh² → 9`, `S²/m → 16/3`,
`λ₂G → 11/3`, **`gap → 2/3`** — all exact. Numerically `gap = 0.666781` at `N = 200000`.

With the proven `eff → 2` (antisymmetric resolvent, twins: response on `a,b` only, `φ = (e_a−e_b)/(2−λ)`,
`eff = 2/(2−λ) = 2`):

> **`λ₂ → 1`, `eff → 2`, `gap → 2/3`, `gap/eff → 1/3`** — all closed-form rationals.

## TASK 3 — `gap/eff = 1/3` is the family minimum

From the low-degree-port sweep (`conjecture_B_typeA_low_degree_ports.md`), the limit `gap/eff`:

- **degree `d` ↑ raises it** (`s=0`: `0.68, 1.22, 1.64, … → 10`); minimum at `d=2`.
- **overlap `s` ↑ lowers it**, bounded by full overlap `s=d` (twins) (`d=2`: `s=0→0.68, s=1→0.52,
  s=2→1/3`).
- **`a~b` raises it** (`d=2,s=0`: `0.68 → 2.06`; the edge shrinks `eff`).
- **denser bulk cannot lower it below 1/3**: `K_N` is the *densest* possible bulk, and bulk-edge
  addition *lowers* `gap/eff` toward the complete-bulk limit (monotonicity study) — so the complete
  bulk is the floor.

Hence the minimizer is `d=2`, `s=2` (twins), `a≁b`, complete bulk, with **`inf gap/eff = 1/3`**
(genuine TYPE A: `f_v₀² = 0.665`, `λ = 1 < γ = 2`). `d=1` (pendant ports) is TYPE B (path), proved
separately.

## TASK 4 — toward Lean

The extremizer's invariants are **exact rationals**: `λ₂ = 1`, `eff = 2`, `gap = 2/3`, `gap/eff = 1/3`
(all as `N→∞`). Two clean, formalisable ingredients:

- **Equitable-partition reduction** — the 4×4 quotient eigenpair lifts to a full eigenpair (standard;
  the quotient gap equals the direct gap, verified exactly here).
- **Closed-form pieces** — `λ₂(N) = 1 + 4/(3N)` from the quotient secular; `eff = 2/(2−λ)` from the
  antisymmetric resolvent.

A sorry-free Lean theorem would state the *limit* `gap → 2/3` for the twin-port family — which needs
the `N→∞` asymptotics of an algebraic (cubic) `λ₂(N)`, so it is a real-analysis + graph-construction
task (heavier than the per-graph identities already formalised). The per-`N` values are
cubic-irrational (only the limit is rational), so the natural Lean target is the asymptotic statement;
deferred, but the quotient structure (rational secular + antisymmetric resolvent) is a clean seed.

## Conclusion

- **Proved (verified symbolically + quotient=direct exactly):** the `d=2` twin-port extremizer has
  `λ₂ → 1`, `eff → 2`, `gap → 2/3`, `gap/eff → 1/3` as `N → ∞`.
- `gap = 4p² = 2/3` comes from `λ₂G = 11/3` (= `1·(9 − 16/3)`) minus `B2′ = 3`, with the Fiedler
  `(x,p,c,r) = (2,1,−2/N,−4/N)/√6`.
- This is the explicit, closed-form extremizer of `gap/eff` over TYPE A: **`gap/eff ≥ 1/3`** with
  equality in the twin-port limit. `gap > 0` is safe (`gap → 2/3`). The TYPE A open lemma is now a
  single sharp inequality with a *known extremizer and value*.

## Lean
No new lemma yet (the result is an `N→∞` limit). `CONJECTURE_B_STATUS.md` open lemma stands at
`gap/eff ≥ 1/3`, extremizer `d=2` twin ports (`λ=1, eff=2, gap=2/3` proved here).
