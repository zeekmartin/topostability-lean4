# Conjecture B — toward `C ≥ −λ` (the leaf as a single scalar inequality)

Target: `C ≥ −λ` where `C = ½(A+I) = Σ_e(d_h−d_l)f_h(f_h−f_l)` (h = higher-degree endpoint), equivalent
to the leaf `B2′ ≤ 2λ·degQuad` (`B2′_unord = λ(d_eff−1) − C`). **Result: `C ≥ −λ` holds 46/46 with a
genuine MARGIN (min `C/λ = −0.69`, not tight at −1); the clean vertex form `A = Σ_v(d_v²−s_v)f_v²` is
exact; but both Cauchy–Schwarz routes FAIL (too weak, `Q/λ` up to 189) and per-vertex non-negativity
FAILS — so `C ≥ −λ` remains genuinely spectral, though the margin means a non-tight proof would
suffice.** Code: [`conjecture_B_C_ge_minus_lambda.py`](../conjecture_B_C_ge_minus_lambda.py).

## TASK 1 — vertex form of `A` (exact)

`d_v² − s_v = Σ_{u∼v}(d_v − d_u)` (`s_v = Σ_{u∼v}d_u`, neighbor-degree sum), so

> **`A = Σ_v (d_v² − s_v) f_v²`** (verified, err `2.8·10⁻¹³`) — a pure vertex sum, no neighbor
> `f`-sums (the Fiedler equation is already absorbed in `W = 2λd_eff − A`).

`I = Σ_e|d_a−d_b|g²` stays an edge sum (the `|·|` has no vertex form). `C = ½(A + I)` verified
(err `3.5·10⁻¹³`).

## TASK 5 — `C ≥ −λ` holds with MARGIN

`C ≥ −λ` : **46/46** (including degenerate `cocktail₆`, `K_{3,3,3}`). Tightest:

| graph | class | `C/λ` |
|---|---|---|
| deg2+dense(80,.3) | TYPE A | **−0.692** |
| deg2+dense(30,.3) | TYPE A | −0.622 |
| deg2+dense(50,.3) | TYPE A | −0.529 |

> **`C ≥ −λ` is NOT tight** — the observed minimum is `−0.69λ`, a uniform margin of `≥ 0.31λ`. (The
> `K_n` tightness of the *`B2′` ratio* `→ 1` comes from the `(d_eff−1)/d_eff` factor, not from `C`:
> `C = 0` at `K_n`.) **A non-tight proof — any constant `≥ 0.7` in `C ≥ −cλ` — would close the leaf.**

## TASK 3 — Cauchy–Schwarz routes FAIL (too weak)

`C = Σ_e(d_h−d_l)f_h·g_e`, two CS splits:

| CS bound | sufficient condition | holds | max |
|---|---|---|---|
| `\|C\| ≤ √Q·√λ`, `Q = Σ(d_h−d_l)²f_h²` | `Q/λ ≤ 1` | **15/46** | **188.9** |
| `\|C\| ≤ √(J·I)`, `J = Σ(d_h−d_l)f_h²` | `J·I/λ² ≤ 1` | **13/46** | **59.0** |

> Both **fail badly** — the `(d_h−d_l)`-weighted sums (`Q`, `J`) blow up (`Q/λ` up to 189 on
> deg2+dense). Cauchy–Schwarz discards the eigenvector structure; consistent with the scale-free product
> form being false for arbitrary `f`. **The CS route is ruled out.**

## TASK 4 — per-vertex representation: no per-vertex bound

Grouping `C = Σ_v c_v` by the higher-degree endpoint, `c_v = f_v Σ_{u∼v, d_u<d_v}(d_v−d_u)(f_v−f_u)`:

> **`c_v ≥ 0` fails** (only 14/46 graphs have all `c_v ≥ 0`); min `c_v/λ = −0.37` (deg2+dense(80,.3)).
> So `C ≥ −λ` is irreducibly a **global sum** — some vertices contribute negatively, bounded only in
> aggregate. No per-vertex lower bound exists.

## Structure recap (why elementary routes fail)

`C = λd_eff − Σ_e min·g²` (so `C ≥ −λ` *is* the leaf). `C = ½(A + I)` with `A` (assortativity, large
negative) and `I` (imbalance, large positive) nearly cancelling. CS and per-vertex both break the
`A↔I` cancellation / the eigenvector coupling, so both fail — the same obstruction as `F`/`W`. The two
exact handles that survive: the **vertex form `A = Σ_v(d_v²−s_v)f_v²`** and the **margin `C ≥ −0.69λ`**.

## Conclusion

- **`A = Σ_v(d_v²−s_v)f_v²`** (exact vertex form) and **`C ≥ −λ` with margin** (`min C/λ = −0.69`,
  46/46 incl. degenerate) are the new handles.
- **CS routes FAIL** (`Q/λ` up to 189; `J·I/λ²` up to 59) — too weak, ruled out.
- **No per-vertex bound** (`c_v ≥ 0` fails 14/46) — `C ≥ −λ` is a global sum.
- `C ≥ −λ` remains genuinely spectral, but the **0.31λ margin** means a *non-tight* proof suffices —
  the most promising remaining handle.

## Lean
The leaf `B2prime_le_two_lam_degQuad` `⟺ C ≥ −λ` `⟺ A + I ≥ −2λ`. The exact vertex form
`A = Σ_v(d_v²−s_v)f_v²` is formalisable (it is the `W = 2λd_eff − A` identity, pure algebra). The open
inequality is `C ≥ −λ` (margin `0.31λ`); CS and per-vertex routes are ruled out. Regular `A = I = 0`
remains the proven anchor (`B2prime_le_two_lam_degQuad_regular`).
