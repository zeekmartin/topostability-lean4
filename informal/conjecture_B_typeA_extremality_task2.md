# TYPE A extremality — TASK 2: `g(d,s)` decreasing in overlap `s` (twins minimize)

Ports `a,b` in `K_N` (`a≁b`), each degree `d`, overlap `s = |N(a)∩N(b)|`; `v₀ ~ {a,b}`. Prove
`g(d,s) := lim_{N→∞} gap/eff` is strictly decreasing in `s`, so `s=d` (twins) minimizes it. Code:
[`conjecture_B_typeA_extremality_task2.py`](../conjecture_B_typeA_extremality_task2.py).

## TASK 2a — the 5-class equitable quotient

Symmetric Fiedler (`f_a=f_b=p`; by `a↔b` symmetry the exclusive vertices share one value). Classes
`{v₀}(x), {a,b}(p), common(s)(c), exclusive = a-only∪b-only (2(d−s))(e), rest(N−2d+s)(r)`. **This is
equitable:** an a-only and a b-only vertex have identical neighbour-counts to every class
(`{a,b}:1, common:s, exclusive:2(d−s)−1, rest:N−2d+s`), so they merge into one class.

Row equations (`Lf = λf`): `(2−λ)x = 2p`; `(d+1−λ)p = x + sc + (d−s)e`;
`(N−s+2−λ)c = 2p + 2(d−s)e + (N−2d+s)r`; `(N−2d+2s+1−λ)e = p + sc + (N−2d+s)r`;
`(2d−s−λ)r = sc + 2(d−s)e`.

## TASK 2b — `λ₂` and `eff` are `s`-independent

In the limit (`c,e,r ~ 1/N`), the `sc,(d−s)e` terms drop from the `a`-row, so `(d+1−λ)p = x` and
`(2−λ)x = 2p` ⇒ **`λ² − (d+3)λ + 2d = 0`** — the *same* secular as the twins, **independent of `s`**.
So `λ₂(d,s) = λ₂(d) = ½(d+3−√(d²−2d+9))`.

The antisymmetric response to `e_a − e_b` (`φ_a=−φ_b=q`, exclusive `±m`, common/rest `0`): the
exclusive equation gives `(N+1−λ)m = q ⇒ m → 0`, so the `a`-row reduces to `(d−λ)q = 1`. Hence

> **`eff(d,s) → 2/(d−λ) = eff(d)`, independent of `s`.** (Verified: `eff` varies only at `O(1/N)`.)

So the whole `s`-dependence of `g = gap/eff` sits in **`gap`**.

## TASK 2c — `gap(d,s)` is LINEAR decreasing in `s`

The leading-order eigenvector (`x = 2p/(2−λ)`, `p² = (2−λ)²/(4+2(2−λ)²)`, both `s`-independent):
`c = 2p(λ−d)/(Nλ)`, `e = p(λ−2d)/(Nλ)`, `r = −2pd/(Nλ)`, giving `c−e = p/N`, `c−r = 2p/N`,
`e−r = p/N`. Summing over edge classes (limit `N→∞`):

- **`T(d,s) = 2(d²+s)·p²`** — *increases* with `s` (more overlap ⇒ more triangles).
- **`B2′(d,s) = 2p²λ²/(2−λ)² + 2d²p² + (2d+2s)·p²`** — *increases* with `s` by `2p²·s`.
- **`λ₂G = λ·(2(x+p)² + 2dp²)`** — **`s`-independent** (the `s/(d−s)` split of `a`'s neighbours both
  give `p²`, summing to `2dp²` regardless of `s`; bulk terms cancel against `S²/m`).

Therefore

> **`gap(d,s) = λ₂G − B2′ = C(d) − 2p²·s`**, with `C(d) = λ(2(x+p)²+2dp²) − 2p²λ²/(2−λ)² − 2d²p² −
> 2dp²` — **linear, strictly decreasing in `s`** (slope `−2p² < 0`).

Verified: `gap` vs `s` is linear to `≤2·10⁻⁴` (finite-`N` noise); slopes `−0.209, −0.134, −0.090` for
`d=3,4,5`.

## TASK 2d — monotonicity

`g(d,s) = gap(d,s)/eff(d) = [C(d) − 2p²s]/eff(d)`, **linear in `s` with slope `−2p²/eff(d) < 0`**.
Hence `g(d,s)` is **strictly decreasing in `s`**, and its minimum over `0 ≤ s ≤ d` is at **`s = d`
(twins)**. (Verified: slope `g` `= −2p²/eff` — `d=2`: pred `−0.1667`, num `−0.163`; `d=3`: `−0.183`
vs `−0.179`; `d=4`: `−0.174` vs `−0.171`.)

## TASK 2e — exact `d=2`

`λ=1`, `p²=1/6`, `eff=2`, `C(2)=4/3`:

> **`gap(2,s) = 4/3 − s/3`**, **`g(2,s) = 2/3 − s/6`**: `g(2,0)=2/3, g(2,1)=1/2, g(2,2)=1/3`.

Numerics (`N=800`): `g = 0.675, 0.512, 0.347 → 2/3, 1/2, 1/3` (favourable `O(1/N)` from above). The
minimum `s=2` gives `1/3` — the twin-port extremizer.

## Conclusion

> **TASK 2 proved:** `eff(d,s)` is `s`-independent (`= 2/(d−λ)`), and `gap(d,s) = C(d) − 2p²s` is
> **linear decreasing** in `s`. Hence `g(d,s)` is strictly decreasing in `s`, **minimized at `s=d`
> (twins)**. With TASK 1 (`g(d,d)` increasing in `d`, min `d=2`), the joint minimum over `(d,s)` is
> `d=2, s=2`, `g = 1/3`.

Monotonicities **(i)** and **(ii)** of the extremality plan are done. The linearity `gap = C(d) − 2p²s`
is the clean structural fact: **overlap raises `B2′` by `2p²` per shared port while leaving `λ₂G`
fixed**, so the gap shrinks linearly — twins (maximal overlap) are the family minimum. Remaining: **(iii)**
`a~b` raises `g`, and **(iv)** complete bulk minimizes (bulk rigidity).

## Lean
The 5-class quotient, the `s`-independent secular `λ²−(d+3)λ+2d=0`, and the linearity `gap = C(d)−2p²s`
are clean equitable-partition facts. The slope `−2p²/eff < 0` (hence monotonicity) needs only `p²>0`,
`eff>0` — formalisable; the `N→∞` limit is the deferred analytic part (as in TASKS 1, twin-port).
