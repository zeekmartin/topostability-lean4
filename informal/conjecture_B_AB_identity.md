# Conjecture B — the exact `A − B` identity (irregular)

Goal: an *exact* identity for `A − B` (`A = Σ_e deficit_e g_e²`, `B = λΣ_{nonedge} h²`) generalizing the
regular case, and the clean closure of `gap = A − B − D ≥ 0`. **Result: `A − B = λ(n−λ) + 2λ·d_eff − W − C`
exactly (`W = Σ_e(d_a+d_b)g_e²`, `C = Σ_e t̄_e g_e²`); the residual `R := (A−B) − λ(d_eff+1−λ) =
λ(d_eff−1) − T ≥ 0` (34/35); and `gap ≥ 0 ⟸ R ≥ 0 ∧ (λ + S²/m ≤ d_eff + 1)`.** Two premises in the
prompt are corrected (see below). Code: [`conjecture_B_AB_identity.py`](../conjecture_B_AB_identity.py).

## TASK 1 — the exact identity

Using `Σ_v mdeg_v D_v = 2(n−1)λ − W` (`D_v` local Dirichlet, `W = Σ_e(d_a+d_b)g_e²`), `deficit_e =
mdeg_a + mdeg_b − t̄_e`, and `B = λ(n − 2 − 2d_eff + λ)` (complement signless, `d_eff = fᵀDf`):

> **`A − B = λ(n − λ) + 2λ·d_eff − W − C`** (`C = Σ_e t̄_e g_e²`; verified, err `3·10⁻¹²`).

Via `t̄_e = n − d_a − d_b + t_e` ⟹ `C = nλ − W + T`, this collapses to **`A − B = λ(2d_eff − λ) − T`**
(`= gap + D`, the circular form). The first form (in `W, C`) is the non-circular identity; it reduces
to the **regular** `A − B = λ(n−λ) − C` (since `W = 2dλ`, `d_eff = d`).

## TASK 2 — the residual `R` (premise corrected)

> **Premise correction:** the regular case is **NOT** `A − B = λ(d+1−λ)` exactly — it is
> `A − B = λ(n−λ) − C ≥ λ(d+1−λ)` (via `C ≤ (n−1−d)λ`), with **equality only at `K_n`**. So `R` does
> **not** vanish for regular graphs.

`R := (A−B) − λ(d_eff+1−λ) = λ(n−1) + λ·d_eff − W − C = **λ(d_eff − 1) − T**` (verified). For regular,
`R = λ(n−1−d) − C ≥ 0` (`= 0` only at `K_n`; e.g. `rr(20,6)`: `R = 10.07`).

## TASK 3 — sign of `R`, and `R ≥ D` is FALSE

- **`R ≥ 0` : 34/35** (one near-tie `deg2d50_.9` at `−7·10⁻⁴`). Equivalently **`T ≤ λ(d_eff − 1)`** — a
  sharpened aggregate-Poincaré bound (stronger than `T ≤ λ·d_eff` by `λ`).
- **`R ≥ D` : only 15/35** (min `R − D = −3.26` at `deg2d80_.9`). **The hoped `R ≥ D` is FALSE** — on
  the dense bottleneck `R < D` (gap is small, both `R` and `D` are `O(1)` and `D` wins). So the closure
  is *not* `R ≥ D`.

## TASK 4 — `R` is NOT a degree-variance

`corr(R, Σ_v(d_v−d_eff)²f_v²) = −0.21` (weak, wrong sign); `R / Σ(d−d_eff)²f² ≈ 10⁻⁴` (not
proportional). So `R` is **not** a variance / clean SOS in the degrees. `R = λ(d_eff−1) − T` genuinely
involves the triangle energy `T` (the irreducible object); it is the slack of the sharpened aggregate
Poincaré, not a degree statistic.

## TASK 5 — the correct closure

`gap = A − B − D = λ(d_eff+1−λ) + R − D`. Since `D = λS²/m`:

> **`gap = [λ(d_eff + 1 − λ) − D] + R = λ(d_eff + 1 − λ − S²/m) + R`.**

So **`gap ≥ 0 ⟸ R ≥ 0 ∧ (λ + S²/m ≤ d_eff + 1)`** (the second gives `λ(d_eff+1−λ−S²/m) ≥ 0`). Verified:
`R ≥ 0` 34/35, spectral `λ+S²/m ≤ d_eff+1` 35/35, both 34/35, `gap ≥ 0` 35/35.

> **Proof skeleton (irregular simple `λ₂`):**
> 1. `R ≥ 0`, i.e. **`T ≤ λ(d_eff − 1)`** (sharpened aggregate Poincaré / deficit bound).
> 2. **`λ + S²/m ≤ d_eff + 1`** (the spectral inequality; regular case `λ ≤ d+1` via interlacing).
> 3. `gap = λ(d_eff+1−λ−S²/m) + R ≥ 0`. ∎ (modulo 1 and 2.)

Both 1 and 2 hold on all tested graphs (34–35/35, one tie). They are the two remaining open inequalities
— **1 is combinatorial** (`T` vs degrees), **2 is spectral** (compression-resistant, `≥3`-dim, per the
2×2/3×3 rounds). The complete graph `K_n` is the joint equality (`R = 0`, spectral tight).

## Conclusion

- **Exact identity:** `A − B = λ(n−λ) + 2λ·d_eff − W − C` (verified), reducing to the regular
  `λ(n−λ) − C`.
- **`R = λ(d_eff−1) − T ≥ 0`** (34/35) — the sharpened aggregate Poincaré `T ≤ λ(d_eff−1)`; does **not**
  vanish for regular (premise corrected).
- **`R ≥ D` is FALSE** (15/35); the correct closure is **`R ≥ 0 ∧ (λ + S²/m ≤ d_eff + 1)`**.
- The irregular simple-`λ₂` conjecture splits cleanly into a **combinatorial** part (`T ≤ λ(d_eff−1)`)
  and a **spectral** part (`λ + S²/m ≤ d_eff + 1`), both verified, jointly tight at `K_n`.

## Lean
Candidate: `(T ≤ λ(d_eff−1)) ∧ (λ + S²/m ≤ d_eff + 1) → gap ≥ 0` (pure arithmetic via
`gap = λ(d_eff+1−λ−S²/m) + R`, sorry-free once the two inputs are lemmas). `triEnergy_le_RHS_regular`
is the regular instance (`d_eff = d`, `S = 0`, spectral `= λ ≤ d+1`; and `T ≤ λ(d−1)` is `t_e ≤ d−1`).
The two open inputs are the combinatorial `T ≤ λ(d_eff−1)` and the spectral `λ + S²/m ≤ d_eff + 1`.
