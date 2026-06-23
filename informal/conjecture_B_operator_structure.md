# Conjecture B — operator structure of `Q = λD − L_t` on the Fiedler eigenspace

Investigate WHY `Q = λD − L_t` is PSD on `E_{λ₂}` (`fᵀQf ≥ 0` for Fiedler `f`) but not globally — no new
degree/count bounds, only operator structure. **Result: the lossless S-procedure
`Q + (L−λI)M + M(L−λI) ⪰ 0` is FEASIBLE on all tested graphs (8/8) — direct evidence that `Q` is PSD
*modulo the Fiedler constraint* `(L−λI)f = 0`. The geometric reason: the Fiedler vector is nearly
orthogonal to `Q`'s negative eigenspace (overlap ≤ 0.09). BUT there is no clean structure: `L_t` does NOT
preserve `E_{λ₂}` (large commutator `[L_t,L]`), `Qf` leaves `E_{λ₂}`, and the S-procedure multiplier `M`
blows up (×10⁶) for irregular graphs — clean (`M = cL`, c≈1) only for `K_n`/cocktail where `Q` is already
near-PSD.** Code: [`conjecture_B_operator_structure.py`](../conjecture_B_operator_structure.py).

## TASK 1 — spectrum of `Q`; Fiedler vs negative directions

| graph | `fᵀQf` | min eig `Q` | #neg | overlap(f, neg eigsp) |
|---|---|---|---|---|
| `K₁₂` | 12.0 | +12.0 | 0 | — |
| cocktail₆ | 20.0 | +4.0 | 0 | — |
| `rr(20,6)` | 12.55 | **−0.31** | ≥1 | 0.09 |
| deg2+dense(40,.6) | 1.96 | **−498.5** | many | **2·10⁻⁴** |
| twin-port `K₃₀` d2 | 2.81 | **−813.6** | many | small |
| gnp(30,.5) | 44.0 | **−53.0** | many | small |

> **`Q` is wildly indefinite on irregular graphs** (min eig down to `−814`), yet **the Fiedler is nearly
> orthogonal to `Q`'s negative eigenspace** (overlap ≤ 0.09; `2·10⁻⁴` on deg2+dense). The Fiedler
> "threads" through `Q`'s positive cone — its tiny projection onto the deep negative directions is
> outweighed by the positive part, giving `fᵀQf > 0`. This is the geometric content of the
> eigenspace-PSD.

## TASK 3 — `L_t` does NOT preserve `E_{λ₂}` (no invariant subspace)

| graph | `‖[L_t,L]f‖` | `‖(I−P_E)L_t f‖` (leaves `E_{λ₂}`) | `‖L_t f‖` |
|---|---|---|---|
| `K₁₂` | 0 | 0 | 120 |
| deg2+dense(40,.6) | **550** | **21.2** | 21.4 |
| twin-port `K₃₀` d2 | **955** | **31.0** | 31.0 |

> For irregular graphs `[L_t, L]f` is large and `L_t f` leaves `E_{λ₂}` almost entirely
> (`‖(I−P_E)L_t f‖ ≈ ‖L_t f‖`). So `L_t` (hence `Q`) does **not** commute with `L` and does **not**
> preserve the Fiedler eigenspace — there is no invariant-subspace / simultaneous-diagonalization
> structure to exploit. (For `K_n`/cocktail, `L_t = (n−2)L` commutes, commutator `= 0`.)

## TASK 2 — `Qf` leaves `E_{λ₂}`

`r = Qf`: the in-eigenspace part `P_E r = (fᵀQf)·f` (simple `λ₂`) is small, the out-of-eigenspace part is
large:

| graph | `‖P_E r‖` | `‖(I−P_E)r‖` |
|---|---|---|
| deg2+dense(40,.6) | 1.96 | **19.85** |
| twin-port `K₃₀` d2 | 2.81 | **30.98** |

> `Qf` is mostly *outside* `E_{λ₂}` — `Q` maps the Fiedler far off the eigenspace. The bound `fᵀQf ≥ 0`
> uses only the (small) in-eigenspace projection, which the constraint isolates.

## TASK 4 — the S-procedure certificate (PSD modulo the constraint)

`fᵀQf ≥ 0 ∀ f ∈ ker(L−λI) ⟺ ∃ symmetric M: Q + (L−λI)M + M(L−λI) ⪰ 0` (the multiplier terms vanish on
`E_{λ₂}`). Searching `M = aI + bD + cL`:

| graph | min eig `Q` (no `M`) | best min eig (with `M`) | `M = (a,b,c)` |
|---|---|---|---|
| `K₁₂` | +12.0 | 12.0 | `(0,0,1.06)` — **clean** |
| cocktail₆ | +4.0 | 20.0 | `(0,0,1.04)` — **clean** |
| `rr(20,6)` | −0.31 | 12.55 | `(−1.9·10⁷, 5.6·10⁵, 5.4·10⁶)` |
| deg2+dense(40,.6) | −498.5 | 1.96 | `(−9·10⁵, 0.88, 9·10⁵)` |
| twin-port `K₃₀` d2 | −813.6 | 2.81 | `(−3.8·10⁵, 1.07, 7.2·10⁵)` |

> **The S-procedure is FEASIBLE on all 8 graphs** — `Q + (L−λI)M + M(L−λI) ⪰ 0` with the achieved
> min-eig equal to `fᵀQf` (the eigenspace minimum). This is **exactly the statement that `Q` is PSD
> modulo the Fiedler constraint** — the central evidence sought. *However*: the multiplier `M` is clean
> (`M ≈ L`) only for `K_n`/cocktail (where `Q` is already near-PSD); for irregular graphs `M` **blows up
> (×10⁶)**. The blow-up means the lossless S-procedure attains its value only in a degenerate limit (the
> multiplier amplifies the weak spectral gap `(L−λI)` to lift `Q`'s deep negative directions) — there is
> **no clean finite multiplier**, no low-rank correction.

## TASK 5/6 — interpretation

`Q ⪰ 0 on E_{λ₂}` is genuinely a **constrained PSD** (S-procedure), confirmed feasible (8/8) — `Q` is
PSD *modulo* `(L−λI)`. The structure is:
- **No invariant subspace** (`[L_t, L] ≠ 0`, `L_t` doesn't preserve `E_{λ₂}`);
- **No low-rank correction** (`Q`'s negative part is high-rank, min-eig `−814`);
- **No clean multiplier** (S-procedure `M` blows up ×10⁶ for irregular);
- The certificate is essentially the eigenspace projection itself, with the Fiedler **nearly orthogonal
  to `Q`'s negative eigenspace** (overlap ≤ 0.09) as the geometric reason.

So the eigenspace-PSD is *barely* true (the Fiedler skims just above `Q`'s deep negative cone), and its
only certificate is the constraint `(L−λI)f = 0` itself (via the lossless but degenerate S-procedure) —
which is why every coarse-graining (degree, count, covariance, entropy, matrix-power) failed: the
magnitude lives in the *precise spectral alignment* of `f` with `Q`'s positive cone, not in any
aggregate or low-complexity invariant.

## Conclusion

- **PSD-modulo-constraint confirmed:** the S-procedure `Q + (L−λI)M + M(L−λI) ⪰ 0` is feasible (8/8) —
  `Q = λD − L_t` is PSD modulo `(L−λI)f = 0`, the central evidence sought.
- **But no clean structure:** `L_t` doesn't preserve `E_{λ₂}` (large commutator), `Qf` leaves it, the
  negative part is high-rank, and the multiplier `M` blows up (×10⁶, clean only for `K_n`/cocktail).
- **Geometric reason:** the Fiedler is nearly orthogonal to `Q`'s negative eigenspace (overlap ≤ 0.09).
- The eigenspace-PSD is an irreducible *constrained* PSD; its certificate is the Fiedler constraint
  itself — explaining why all coarse-grained routes lose the magnitude.

## Lean
No code change: the S-procedure certificate exists (PSD modulo `(L−λI)`) but with a non-clean (blown-up)
multiplier, so it is not a finite Lean lemma. `aggregate_triangle_poincare` stays the direct sorry; the
operator-theoretic content is "`Q` PSD modulo the Fiedler constraint," confirmed but not finitely
certifiable here. 3 sorrys unchanged.
