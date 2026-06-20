# Conjecture B — a deterministic core-gap stability lemma for the degree-2 bottleneck

Replace "random density `q`" with **deterministic core assumptions**: a degree-2 vertex `v₀` attached
to `a, b` in a core `H` with **spectral gap `γ = λ₂(H)`** and degrees in `[δ, Δ]`. `f` = Fiedler of
`G = H + v₀` (`Lf = λ₂f`, `f ⊥ 1`, `λ₂ ≈ 2 ≪ γ`). Code:
[`conjecture_B_core_gap_stability.py`](../conjecture_B_core_gap_stability.py); tested on complete,
`gnp(·,q)` (q=0.3,0.5,0.65,0.9), random-regular, circulant, and cycle cores at `m = 100, 300`.

## The exact resolvent identity

Restricting `Lf = λ₂f` to the core vertices `u ∈ H`:

> **`(L_H − λ₂I) f_H = −(f_a − f_v₀)e_a − (f_b − f_v₀)e_b =: source`** (a 2-sparse RHS).

Writing `f_H = c·1_H + f_H^⊥` (`f_H^⊥ ⊥ 1_H`, `c = −f_v₀/(n−1)` from `f ⊥ 1`), and using that
`L_H − λ₂I` has eigenvalues `≥ γ − λ₂ > 0` on `1_H^⊥`:

> **`‖f_H^⊥‖ ≤ ‖source‖/(γ − λ₂)`**,  `‖source‖ = √((f_a−f_v₀)² + (f_b−f_v₀)²)`.

This is the deterministic replacement for the random resolvent — the **core spectral gap `γ` controls
the attachment values**. (Verified `16/16`: `|f_a − c| ≤ ‖source‖/(γ−λ₂)`.)

## The three bounds (tested across all core types)

| core | γ | Δ | `(|f_a|+|f_b|)·γ/|f_v₀|` | `|C_att|·γ/(Δf_v₀²)` | `R″/|C_att|` | gap |
|---|---|---|---|---|---|---|
| K₁₀₀ | 100 | 99 | 0.000 | 0.000 | ∞ (`C_att=0`) | 0.198 |
| gnp(100,0.3) | 15.1 | 42 | 0.752 | 0.511 | 1.23 | 0.496 |
| gnp(100,0.65) | 51.1 | 76 | 0.516 | 0.440 | 1.42 | 0.340 |
| gnp(300,0.5) | 121.6 | 178 | 0.895 | 0.713 | **1.04** | 0.105 |
| randreg(300,90) | 74.6 | 90 | 1.196 | 1.173 | 1.07 | 0.114 |
| circ(300,±1..75) | 53.5 | 148 | 0.381 | 0.377 | 1.05 | 0.063 |
| cycle₁₀₀ | 0.004 | 2 | 0.008 | 0.000 | 153 | 0.012 |

> **(1) `|f_a| + |f_b| ≤ C·|f_v₀|/γ`** — `C ≈ 1.2` (max ratio over all cores; rigorous form
> `‖f_H^⊥‖ ≤ ‖source‖/(γ−λ₂)` holds 16/16).
> **(2) `|C_attach| ≤ C·Δ·f_v₀²/γ`** — `C ≈ 1.2` (max ratio 1.17). From (1) and `|d_h−d_l| ≤ Δ−1`:
> `|C_attach| ≤ (Δ−1)(|f_a|+|f_b|)(|f_a|+|f_b|+2|f_v₀|)`.
> **(3) `R″ ≥ |C_attach|`** — holds 16/16; hence `gap = R″ + C_attach + C_dense ≥ 0`.

## Reading the bounds

- **`|C_attach| = O(Δ f_v₀² / γ)`.** For a good-expander core (`γ ≍ Δ`, e.g. `gnp`, random-regular)
  this is `O(f_v₀²) = O(1)` — the `O(1)` negative term seen in the q<1 analysis, now *deterministic*.
  For a complete core `γ = Δ + 1` and in fact `C_attach = 0` exactly (`f_a = f_b = 0`, the q=1 case).
- **The margin `R″/|C_attach| ≥ 1.04`**, tightest on large dense `gnp`/random-regular (`γ/Δ ≈ 0.5–0.8`)
  — the asymptotically extremal regime. For poor-expander cores (`cycle`, `γ → 0`) the bound (1) is
  vacuous, but `C_attach ≈ 0` anyway (uniform degree-2, no degree gradient), so `gap = R″ > 0`
  trivially. So the lemma's content lives in the **dense-core** regime.
- **`C_dense`** (the core's internal degree gradient) is small: `≤ 0.05` even for "regular" cores
  (nonzero only because `a, b` get degree `+1` from `v₀`); `C` is dominated by `C_attach`.

## What is rigorous, what is open

- **Rigorous (linear algebra + spectral gap):** the resolvent identity and `‖f_H^⊥‖ ≤
  ‖source‖/(γ−λ₂)`, hence **(1)** `|f_a|+|f_b| ≤ |f_v₀|/(n−1) + √2|f_v₀|/(γ−λ₂−√2)` and **(2)**
  `|C_attach| ≤ (Δ−1)(|f_a|+|f_b|)(|f_a|+|f_b|+2|f_v₀|) ≤ C·Δf_v₀²/γ`. These *deterministically*
  bound the only negative contribution in terms of `γ, Δ, f_v₀`.
- **Open (the conjecture-strength step):** **(3)** `R″ ≥ |C_attach|`. It holds on all tested cores
  (margin `≥ 1.04`), but proving it needs a *lower bound on `R″`* matching the `O(Δf_v₀²/γ)` upper
  bound on `|C_attach|` — i.e. a quantitative `R″ ≳ Δf_v₀²/γ`. This is the residual difficulty,
  reduced from "prove `gap ≥ 0`" to "prove `R″` clears the explicitly-bounded `|C_attach|`".

## Conclusion

The random `q` is replaced by a **deterministic core-gap stability lemma**: for a degree-2 bottleneck
on a core with spectral gap `γ` and max degree `Δ`,
- `|f_a| + |f_b| ≤ C|f_v₀|/γ` (rigorous resolvent bound),
- `|C_attach| ≤ C·Δ f_v₀²/γ` (the only negative contribution, deterministically controlled),
- `gap = R″ + C ≥ 0` reduces to `R″ ≥ |C_attach|` (verified 16/16; the remaining open step).

This isolates the difficulty to a single, explicitly-quantified inequality `R″ ≳ Δf_v₀²/γ`, and shows
the bottleneck mechanism is governed entirely by the **core spectral gap `γ` vs max degree `Δ`** —
no randomness needed. The complete-core (`γ = Δ+1`, `C_attach = 0`) is the exactly-solvable, tightest
instance.

## Lean
No new lemma this round. The rigorous resolvent bound (1) is connectable to Paper16's
`poincare_on_block` (a resolvent/Courant-Fischer bound of the same `‖·‖ ≤ ‖g‖/(γ−λ)` form), but
wiring it to the `G = H + v₀` construction (induced Laplacian `L_H`, its spectral gap `γ`) needs
induced-subgraph spectral infrastructure beyond the current dev. The exact restriction identity
`(L_H − λ₂I)f_H = source` is the formalisable core, deferred.
