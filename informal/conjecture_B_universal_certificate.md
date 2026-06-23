# Conjecture B — is the S-procedure constant `c` universally bounded?

Test whether `Q + 2cL(L−λI) ⪰ 0` (`M = cL`) holds with a *fixed* `c`. **Result: mixed. (1) MAJOR
CORRECTION: the actual `c` is SMALL (`≤ 2.5`), not the `10⁶` of the previous round — that blow-up was a
basis-optimizer artifact; the right multiplier `M = cL` needs only `c ≈ 2`. (2) But the full-PSD `c` is
NOT universally bounded — it grows `~√n` for twin-port (off-diagonal / non-commutativity). (3) HOWEVER
the per-mode Poincaré constant `C = max_k uᵀL_t u/(λ_k uᵀDu)` IS bounded (`≈ 1`, never growing), and the
aggregate is just the Fiedler mode of it. (4) The general (non-spectral) cubic form
`vᵀL_t v·‖v‖² ≤ C(vᵀLv)(vᵀDv)` holds with `C` bounded (`≈ 1`, max `1.35`, decreasing) — but `C > 1` for
twin, so it gives `T ≤ 1.35·λ·degQuad`, not the exact aggregate (`C = 1`).** The aggregate is genuinely
eigenvector-specific. Code:
[`conjecture_B_universal_certificate.py`](../conjecture_B_universal_certificate.py).

## TASK 1/5 — the actual `c` (correcting the `10⁶` artifact)

Bisection for the smallest `c` with `Q + 2cL(L−λI) ⪰ 0`:

| family | `c_PSD` across sizes | `c_PSD/√n` |
|---|---|---|
| `K_n` (n=20→160) | 0, 0, 0, 0 | — (`Q` already PSD) |
| deg2+dense_.6 (n=40→240) | 0.6, 0.6, 0.7, 0.7 | →0 (bounded) |
| **twin-port (n=23→143)** | **1.0, 1.5, 2.1, 2.5** | **≈ 0.22 (const)** |
| gnp_.5 (n=30→120) | 0.1, 0.07, 0.0 | →0 |

> **`c_PSD ≤ 2.5` — the previous round's `10⁶` was a degenerate `{I,D,L}`-basis optimizer artifact.** The
> correct `M = cL` needs only `c ≈ 2`. **But for twin-port `c ~ 0.22√n` (slope 0.51 on log-log) — NOT
> universally bounded** (grows, slowly). `K_n`/gnp need `c → 0` (`Q` already near-PSD); deg2+dense is
> bounded (`c ≈ 0.7`).

## TASK 3/4 — per-mode Poincaré `C` IS bounded (this is the aggregate)

`C = max_{k: λ_k>λ} uᵀL_t u/(λ_k uᵀDu)`:

| family | `C` across sizes | `C/Δ` |
|---|---|---|
| deg2+dense_.6 | 0.62, 0.61, 0.60, 0.61 | →0 |
| twin-port | 0.95, 0.97, 0.99, 0.99 | →0 |
| gnp_.5 | 0.51, 0.52, 0.51 | →0 |

> **`C ≈ 1` is BOUNDED** (never grows; `C/Δ → 0`). This is exactly the *per-eigenmode* aggregate
> `uᵀL_t u ≤ C·λ_k·uᵀDu` — and the Fiedler (`k=1`) instance is `T_unord ≤ C·λ·degQuad` =
> `aggregate_triangle_poincare`. `C < 1` confirms the aggregate holds with a *uniform margin*.

## TASK 2 — why `c_PSD` grows but `C` doesn't: non-commutativity

`Q` does NOT commute with `L` (previous round: `[L_t,L] ≠ 0`), so `Q + 2cL(L−λI)` is **not** diagonal in
the `L`-basis. The *diagonal* entries need only bounded `c ~ C`, but the *off-diagonal* entries (the
non-commutativity) push the full-PSD `c` up to `~√n`. **The √n growth is purely an artifact of demanding
*global* PSD — which is overkill.** The aggregate is just the *single diagonal entry* `fᵀQf ≥ 0`
(Fiedler mode), which has bounded constant `C ≤ 1`.

## TASK 2b — the general (non-spectral) cubic form

`vᵀL_t v·‖v‖² ≤ C(vᵀLv)(vᵀDv)` for *arbitrary* `v` (random sampling):

| family | `C` (n increasing) |
|---|---|
| `K_n` | 0.95, 0.97, 0.99 |
| deg2+dense_.6 | 0.73, 0.69, **0.64** (decreasing) |
| **twin-port** | **1.35, 1.15, 1.12** (decreasing) |
| gnp_.5 | 0.54, 0.53, 0.51 |

> **The general cubic form holds with `C` BOUNDED** (≈ 1, max 1.35 at small twin, *decreasing* with `n`)
> — a genuine *non-spectral* inequality. **BUT `C > 1` for twin** (1.35 → 1.12), so for an eigenvector it
> gives `T_unord ≤ C·λ·degQuad` with `C ≈ 1.1–1.35` — **not the exact aggregate (`C = 1`)**. The exact
> `C = 1` holds *only at eigenvectors* (the aggregate), not for all `v`. So the aggregate is genuinely
> eigenvector-specific; the general form is a bounded near-miss.

## TASK 5 — the Lean situation

- **No fixed-`c` universal certificate:** `c_PSD ~ √n` (twin) — `Q + 2cL(L−λI) ⪰ 0` with a constant `c`
  fails asymptotically.
- **The general cubic form** (`C = 1`) would give the aggregate for all `v`, but `C > 1` (twin 1.35) — it
  is FALSE with `C = 1`. With `C = 2` it is true (and bounded) but gives only `T ≤ 2λ·degQuad` (factor-2
  weak — insufficient for regime i, which needs the exact `T ≤ λ·degQuad`... in Lean ordered:
  `triEnergy ≤ 2λ·degQuad` is the exact target, `= T_unord ≤ λ·degQuad`).
- **The right object** is the per-mode (Fiedler) Poincaré `T_unord ≤ λ·degQuad` (`C = 1`,
  eigenvector-specific), which IS `aggregate_triangle_poincare` — bounded constant `C < 1` empirically,
  but no fixed-`c`/general-`v` reduction proves it (off-diagonal √n, general `C > 1`).

## Conclusion

- **`c_PSD ≤ 2.5` (NOT `10⁶`)** — correcting the previous artifact; `M = cL` with small `c`.
- **`c_PSD ~ √n` for twin** (off-diagonal/non-commutativity) — no fixed-`c` universal certificate, but
  this is overkill (global PSD).
- **Per-mode `C ≈ 1` bounded** (the aggregate, `C < 1` margin); the general cubic `C ≈ 1.35` bounded but
  `> 1` (eigenvector-specific exactness).
- The aggregate is the bounded per-mode constant at the Fiedler; no fixed-`c` operator certificate or
  general-`v` inequality with `C = 1` exists. The exact `C = 1` lives only on eigenvectors.

## Lean
No code change: there is no fixed-`c` certificate (`c ~ √n`) and no general-`v` form with `C = 1`
(`C > 1` off eigenvectors). `aggregate_triangle_poincare` stays the direct sorry — the bounded per-mode
constant `C < 1` confirms it holds with margin, but the exactness (`C = 1`) is eigenvector-specific and
not captured by a constant-`c` or all-`v` inequality. 3 sorrys unchanged.
