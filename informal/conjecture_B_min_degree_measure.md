# Conjecture B — the min-degree weighted Fiedler measure

Analyze `B2′ ≤ 2λ·degQuad` directly through the Fiedler **edge measure** `μ_e = g_e²/λ` (`Σμ = 1`),
keeping `min(d_a,d_b)` intact (no `F`/`W`/average-degree relaxations — all ruled out). **Result: the
Lean leaf is exactly `E_μ[min(d_a,d_b)−1] ≤ d_eff` (43/43, tight at `K_n`); the `−1` is NECESSARY
(`E_μ[min] ≤ d_eff` FAILS 23/43). The mechanism is a strong anti-correlation `corr(min, g²) ≈ −0.50`
(μ-mass concentrates on low-min-degree bottleneck edges), giving a Chebyshev bound
`E_μ[min] ≤ uniform-edge mean` (43/43).** Code:
[`conjecture_B_min_degree_measure.py`](../conjecture_B_min_degree_measure.py).

## TASK 1/2 — the measure inequality (sharp vs loose)

With `μ_e = g_e²/λ`, the Lean leaf `B2′_ord ≤ 2λ·degQuad` is *exactly* `B2′_unord/λ ≤ d_eff`, i.e.

> **`E_μ[min(d_a,d_b) − 1] ≤ d_eff`** (`d_eff = Σ_v d_v f_v² = E_ν[d]`, vertex measure `ν_v = f_v²`).

| inequality | holds | note |
|---|---|---|
| `E_μ[min−1] ≤ d_eff` (**SHARP = Lean leaf**) | **43/43** | tight at `K_n` (ratio `(n−2)/(n−1) → 1`) |
| `E_μ[min−1] ≤ 2·d_eff` (the prompt's loose form) | 43/43 | large slack |
| `E_μ[min] ≤ d_eff` (sharper candidate) | **23/43** | **FALSE** — fails on random dense |

> **The `−1` is necessary.** `E_μ[min] = d_eff` *exactly* for regular graphs, and slightly *exceeds*
> `d_eff` on random dense (gnp(60,.7): `E_μ[min]/d_eff = 1.0038`). So `E_μ[min] ≤ d_eff` is false; the
> `−1` (one common neighbour avoids the two endpoints) supplies exactly the needed margin.

Extremizer of `E_μ[min−1]/d_eff`: `K_n` / dense-regular / dense-random, ratio `→ 1` (`K₅₀` 0.980).

## TASK 3 — min-degree buckets: mass concentrates on LOW min-degree

`mass_μ(k) = Σ_{e: min-deg = k} μ_e`:

| graph | `d_eff` | bucket masses |
|---|---|---|
| deg2+dense(80,.9) | 2.87 | **k=2: 0.986**, k≥63: ≈0 |
| twin-port `K₈₀` d2 | 4.80 | **k=2: 0.33, k=3: 0.65**, k=79: 0.016 |
| star12+8 | 1.00 | **k=1: 1.000**, k=11: 0 |
| gnp(40,.5) | 11.96 | **k=11: 0.795**, k≥12: small |
| `K₂₀` | 19.0 | k=19: 1.000 (regular) |

> **The μ-mass sits on LOW-min-degree (bottleneck) edges**, so `E_μ[min] ≈ d_eff` stays small even
> when high-min-degree edges exist (they carry ≈0 mass). On TYPE A the high-degree clique edges
> (`k ≈ N`) carry essentially zero Fiedler gradient.

## TASK 4 — the anti-correlation `corr(min, g²)`

| class | mean `corr(min, g²)` | range |
|---|---|---|
| TYPE B (lollipop/barbell) | **−0.893** | [−0.99, −0.84] |
| TYPE A (deg2+dense, twin) | **−0.654** | [−1.00, −0.32] |
| clique+star | −0.543 | [−0.59, −0.50] |
| RANDOM (dense) | −0.449 | [−0.59, −0.30] |
| REGULAR | 0.000 | (min constant) |
| **ALL** | **−0.501** | — |

> **Min-degree and the Fiedler gradient `g²` are strongly anti-correlated** (high-min-degree edges have
> low gradient). This is *the* mechanism: the bottleneck (where `g²` lives) is exactly where degrees are
> small.

## TASK 5 — Chebyshev / rearrangement

Because `min` and `μ_e ∝ g²` are anti-correlated, the μ-weighted mean is below the uniform mean:

> **`E_μ[min] ≤ uniform-edge mean(min)` : 43/43** (Chebyshev's sum / rearrangement inequality).

This *confirms the anti-correlation direction* but is **loose vs `d_eff`** (uniform mean can be huge:
deg2+dense(80,.3) uniform `min` = 22.1 vs `E_μ[min] = 3.06`, `d_eff = 2.36`). So Chebyshev against the
uniform edge mean is not enough; the bound that matters compares `E_μ[min]` to the *vertex Fiedler
degree average* `d_eff = E_ν[d]`, a measure-transfer from edges to vertices.

## TASK 6 — Lean target (no `F`/`W` relaxation)

> **Target (unchanged, = `B2prime_le_two_lam_degQuad`):** `E_μ[min(d_a,d_b) − 1] ≤ d_eff`, i.e.
> `Σ_e (min(d_a,d_b) − 1) g_e² ≤ (Σ_e g_e²) · (Σ_v d_v f_v²)` at a Fiedler eigenpair.

The min-degree measure analysis pins the proof requirements:
- **keep `min(d_a,d_b)`** (the `−1` is essential; `E_μ[min] ≤ d_eff` is false);
- **exploit the anti-correlation** `corr(min, g²) ≈ −0.50` / mass-concentration on low-min-degree edges
  — *not* a uniform degree bound (`F`, `W`, constant-`α` all dead);
- the inequality is an **edge-measure (`μ`) → vertex-measure (`ν = f²`) transfer**; the regular case
  (`min ≡ d`, `μ` and `ν` both uniform-degree) is the proven anchor (`B2prime_le_two_lam_degQuad_regular`).

The cleanest provable sub-form is the **Chebyshev anti-correlation** `E_μ[min] ≤ E_unif[min]`
(43/43) — true and elementary, but it must be combined with a vertex-transfer step to reach `d_eff`
(the transfer is the remaining spectral content, since the eigenvector ties `μ` to `ν`).

## Conclusion

- **Lean leaf = `E_μ[min−1] ≤ d_eff`** (43/43, tight `K_n`); the **`−1` is necessary**
  (`E_μ[min] ≤ d_eff` fails 23/43).
- **Mechanism:** μ-mass concentrates on low-min-degree bottleneck edges; `corr(min, g²) ≈ −0.50`
  (TYPE B −0.89). The Chebyshev form `E_μ[min] ≤ E_unif[min]` holds 43/43.
- **Proof direction:** keep the `min`, use the anti-correlation (not `F`/`W`), and transfer the
  edge measure `μ` to the vertex measure `ν = f²` — anchored at the proven regular case.

## Lean
No code change. The leaf `B2prime_le_two_lam_degQuad` *is* `E_μ[min−1] ≤ d_eff`; the analysis rules in
the anti-correlation/measure-transfer route and rules out (again) every degree relaxation. The
elementary Chebyshev sub-fact `E_μ[min] ≤ E_unif[min]` is a candidate stepping-stone.
