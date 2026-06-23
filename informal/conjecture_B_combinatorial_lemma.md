# Conjecture B — the combinatorial lemma `R ≥ 0` (T ≤ λ(d_eff−1)) is NOT a theorem

Target: `R = λ(d_eff−1) − T ≥ 0`, i.e. `T ≤ λ(d_eff − 1)` (`T = Σ_e t_e g_e²`, `d_eff = fᵀDf`,
`λ = Σ_e g_e²`). **Result (correcting the prior two rounds): `R ≥ 0` is FALSE — marginally but
*genuinely* violated (`R ≈ −0.003`, well-conditioned) on very dense deg2+dense graphs (`q ≥ 0.9`).
Moreover all per-edge proof routes (`B2′`, `W`) overshoot by 5–20×, so even where it holds it needs
apex cancellation. The "combinatorial + spectral" split is an *exact identity* but NOT two
sign-definite lemmas.** Code:
[`conjecture_B_combinatorial_lemma.py`](../conjecture_B_combinatorial_lemma.py).

## TASK 1 — `R ≥ 0` is marginally FALSE at the dense limit

`T ≤ λ(d_eff−1)` holds **66/68**, but the 2 "failures" are *real*: dense deg2+dense (`q ≥ 0.9`,
eigengap `30–94`, well-conditioned, `λ₂` simple) give `R < 0`:

| graph | `R = λ(d_eff−1) − T` | eigengap | `R < 0`? |
|---|---|---|---|
| deg2d50_.90 | **−0.0033** | 32.2 | **yes** |
| deg2d50_.95 | **−0.0020** | 36.5 | **yes** |
| deg2d110_.90 | **−0.0013** | 85.4 | **yes** |
| deg2d110_.95 | **−0.0013** | 94.1 | **yes** |
| deg2d80_.80 | +0.012 | 50.5 | no |

> **`R ≥ 0` is NOT a theorem.** As density `→ 1` (`K_n` approach), `R → 0` and dips slightly *below* 0
> (`≈ −0.003`). The violations are well-conditioned (large eigengap, simple `λ₂`) — not numerical. So
> `T ≤ λ(d_eff−1)` fails marginally on the dense bottleneck. (The looser aggregate `T ≤ λ·d_eff` holds
> 68/68.)

## TASK 3/4/5 — every per-edge route overshoots (apex cancellation essential)

| route to `T ≤ λ(d_eff−1)` | holds | min slack |
|---|---|---|
| `B2′ ≤ λ(d_eff−1)` (`T ≤ B2′`) | 39/68 | **−2.76** |
| `W ≤ 2λ·d_eff` (then `B2′ ≤ W/2−λ ≤ λ(d_eff−1)`) | **12/68** | **−210** |

- `T ≤ B2′` (per-edge `t_e ≤ min−1`) and `B2′ ≤ W/2 − λ` (`min ≤ average`) both hold 68/68, but
  `W ≤ 2λ·d_eff` **fails massively** (gnp(60,.7): `W = 2512` vs `2λd_eff = 2302`; deg2+dense:
  `W = 213` vs `11`). So `W/2 − λ ≫ λ(d_eff−1)` (5–20×).
- `B2′ ≤ λ(d_eff−1)` fails 29/68 (the `B2′` wall — `B2′` overshoots `T` on dense graphs).

> **No per-edge bound proves `T ≤ λ(d_eff−1)`** — the `min−1`/degree relaxations are 5–20× too loose.
> The `−λ` sharpening (vs aggregate `T ≤ λd_eff`) comes from **apex cancellation** (the aggregate
> `Σ_c E_c` structure with the Fiedler local-mean constraint), the same deep cancellation as the
> conjecture itself — not from `f ⊥ 1`, edge normalization, or the complement identity alone.

## Consequence — the prior "clean split" is corrected

The exact identity `gap = λ(d_eff+1−λ−S²/m) + R` (last round) holds, but **`R` is not sign-definite**
(dips to `−0.003`). So:

> **The closure `gap ≥ 0 ⟸ R ≥ 0 ∧ (λ+S²/m ≤ d_eff+1)` is INVALID** — `R` can be `< 0`. `gap ≥ 0` holds
> there because the *spectral term* `λ(d_eff+1−λ−S²/m) ≥ 0` (still true, `≥` `|R|`) compensates the
> small negative `R`. Neither the combinatorial nor the effective-degree template
> (`gap ≥ λ(d_eff+1−λ) − D`) is an exact theorem; both are tight approximations failing by `≈ 0.003` at
> the `K_n`-approach.

There is **no universal template constant** `c` with `(A−B) − λ(c−λ) ≥ 0` always: the required
`c ≤ 2d_eff − T/λ` approaches `d_eff + 1` *from below* as density `→ 1`, so `c = d_eff+1` is marginally
too large (by the `R < 0` amount).

## TASK 6 — Lean target status (downgraded)

> `triEnergy_le_lam_mul_degeff_sub_one` (`T ≤ λ(d_eff−1)`) is **NOT a valid lemma** (counterexamples at
> dense deg2+dense). It cannot be a Lean target. The regular instance `T ≤ λ(d−1)` *does* hold
> (`t_e ≤ d−1`, the regular case), but the `d_eff` generalization fails.

So the only exact statements remain: **`gap ≥ 0`** (the conjecture, irregular open), the **regular case**
(`triEnergy_le_RHS_regular`, proven), and the **exact identity** `gap = λ(2d_eff−λ) − T`. The clean
two-lemma split is *not* available — both the combinatorial and effective-degree reformulations are
asymptotically-tight approximations, not theorems.

## Conclusion

- **`R ≥ 0` (`T ≤ λ(d_eff−1)`) is FALSE** — marginally but genuinely (`R ≈ −0.003`, well-conditioned) on
  dense deg2+dense; corrects the prior "R ≥ 0 (34/35)" to "holds except at the `K_n`-approach".
- **No per-edge route proves it** (`B2′`, `W` overshoot 5–20×); the `−λ` sharpening needs apex
  cancellation (as deep as the conjecture).
- **The "combinatorial + spectral" split is an exact identity but not two sign-definite lemmas** — `R`
  is not `≥ 0`; the spectral term compensates. `gap ≥ 0` remains the only exact (open) target, with the
  regular case proven and the irregular case requiring the apex cancellation directly.

## Lean
No new lemma; the candidate `T ≤ λ(d_eff−1)` is *refuted*. The honest target stays `gap ≥ 0` (regular
proven via `triEnergy_le_RHS_regular`; irregular open). The decomposition `gap = λ(2d_eff−λ) − T` is a
clean identity but does not yield a sign-definite split.
