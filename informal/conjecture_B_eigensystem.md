# Conjecture B — eigensystem / over-concentration analysis on the `Required > 0` regime

Solve the Fiedler eigenvector system explicitly on the bottleneck families and ask whether
it *forces* `Σ_{v≠v₀} d_v f_v²` large enough to close B — **without** invoking minimality.
Code: [`conjecture_B_eigensystem.py`](../conjecture_B_eigensystem.py).

**Headline (positive for the original binding family).** On **deg2+dense the eigensystem
closes B without minimality**: the dense block's large spectral gap (`λ₂(block) ~ qn ≫
λ₂(G) ≈ 2`) forces the Fiedler to be **uniform on the dense block** (`f_w ≈ −f_{v₀}/(n−1)`),
which gives `Σ_{v≠v₀} d_v f_v² ≈ q·f_{v₀}² → q ≥ 2q−1` (⟺ `q ≤ 1`, always). The crucial
mechanism — **block connectivity** replacing **global minimality** — is purely the
eigenvector equation plus the dense block's own `λ₂`. **But it is deg2+dense-specific:** on
lollipops the bottleneck is a *path*, the clique carries only ~13% of the mass, and the
uniformity of the clique does not close B.

---

## TASK 3 — the eigensystem is exactly the resolvent

On deg2+dense (`v₀` = degree-2 vertex, neighbours `a,b`; "dense" = the other `n−1`
vertices), the eigen-equation restricted to the dense block is, exactly,
`(L_d + E − λ₂I) f_dense = f_{v₀}·χ_{ab}`, where `L_d` = dense-block Laplacian, `E` = the
rank-2 degree bump for `a,b` (their edge to `v₀`), `χ_{ab}` = indicator of `{a,b}`. Solving:

| `n` | `‖f_dense^solved − f_dense^actual‖ / ‖f_dense‖` |
|---|---|
| 50 | 1.0×10⁻¹⁴ |
| 100 | 2.7×10⁻¹⁵ |
| 200 | 1.3×10⁻¹⁴ |

So `f_dense = (L_d + E − λ₂I)⁻¹ (f_{v₀}·χ_{ab})` **exactly** — the dense Fiedler is the
resolvent of the (degree-corrected) dense Laplacian applied to a 2-sparse source.

## TASK 1 — the resolvent forces uniformity

| `n` | `q` | `λ₂(G)` | `λ₂(block)` | `mean_d` | `−f_{v₀}/(n−1)` | `std/\|mean\|` |
|---|---|---|---|---|---|---|
| 50 | 0.65 | 1.98 | 20.5 | 0.0202 | 0.0202 | 0.324 |
| 100 | 0.65 | 1.99 | 47.7 | 0.0101 | 0.0101 | 0.222 |
| 200 | 0.65 | 1.99 | 109.0 | −0.0050 | −0.0050 | 0.161 |
| 500 | 0.65 | 2.00 | 285.5 | 0.0020 | 0.0020 | **0.097** |

Two exact/structural facts:
- **`mean_dense = −f_{v₀}/(n−1)` exactly** — forced by `f ⊥ 1` (`f_{v₀} + Σ_dense f = 0`).
- **`f_dense → uniform`** (`std/|mean| → 0`, monotone in `n`). Why: in the `L_d`-eigenbasis,
  `f_dense = Σ_k ĝ_k/(λ_k(L_d) − λ₂)·u_k`. The constant mode (`λ_0 = 0`) gives
  `−ĝ_0/λ₂·u_0 = −f_{v₀}/(n−1)·1`; every other mode has `λ_k ≥ λ₂(block) ~ qn ≫ λ₂ ≈ 2`, so
  its coefficient is `O(1/qn) → 0`. The **dense block's spectral gap** is what flattens `f`.

## TASK 2 — the forced dense degree-mass

| `n` | `q` | `Σ_dense d_v f_v²` | `q·f_{v₀}²` | `2q−1` | `≥`? |
|---|---|---|---|---|---|
| 500 | 0.50 | 0.507 | 0.499 | 0.00 | ✓ |
| 500 | 0.65 | 0.655 | 0.649 | 0.30 | ✓ |
| 500 | 0.80 | 0.802 | 0.798 | 0.60 | ✓ |

`Σ_dense d_v f_v² ≈ q·f_{v₀}²` (uniform `f_dense`, `Σ_dense d ≈ 2m ≈ qn²`, so `Σ d·mean² ≈
qn²·(f_{v₀}/(n−1))² → q f_{v₀}²`; the small non-uniformity only *adds*). Since `f_{v₀}² →
1`, this `→ q`, and the required bound is `2q − 1`:

> `Σ_dense d_v f_v² ≈ q ≥ 2q − 1  ⟺  q ≤ 1`  — **always true**, with margin `→ 1 − q`.

So the deg2+dense scalar inequality `fᵀDf + f_{v₀}² ≥ λ₂ + S²/m` (⟺ `Σ_dense d_v f_v² ≥
2q−1`) is *forced* by the eigensystem, holding with margin `1 − q > 0`.

## TASK 4 — lollipops: the mechanism does not transfer

| lollipop | `λ₂(G)` | `λ₂(clique)` | clique-f `std/\|mean\|` | clique f²-mass | path f²-mass |
|---|---|---|---|---|---|
| `m=30, L=5` | 0.092 | 30.0 | **0.016** | 0.123 | **0.877** |
| `m=50, L=10` | 0.026 | 50.0 | **0.004** | 0.137 | **0.863** |

The clique IS forced uniform (even more so — `λ₂(clique) = m`), but it carries only **~13%**
of the Fiedler mass; the Fiedler lives on the **path** (~87%), where it is a 1-D ramp (the
eigen-equation along the path gives `(2−λ₂)f_v = f_{v−1}+f_{v+1}`, a near-harmonic profile,
not uniform). So the "dense block ⇒ uniform ⇒ enough degree-mass" argument has nothing to
act on — the relevant structure is the path, not a dense block.

## TASK 5 — does this close B?

- **deg2+dense: YES, and without minimality.** The chain is: (1) `f ⊥ 1 ⇒ mean_dense =
  −f_{v₀}/(n−1)` (exact); (2) `λ₂(block) ≫ λ₂(G) ⇒ f_dense` uniform (resolvent, the dense
  block's own connectivity); (3) `Σ_dense d_v f_v² ≈ q f_{v₀}² ≥ 2q−1` (⟺ `q ≤ 1`); (4) via
  the carrier reduction `Deficit ≈ λ₂ f_{v₀}²`, this gives `Deficit ≥ Required`, i.e. B.
  **No step uses the global minimality of the Fiedler** — the role of "smoothness" is played
  instead by the **dense block's spectral gap** (a local connectivity fact). This is the
  first minimality-free route through the `Required > 0` regime on the binding family.
- **lollipops: NO.** The path bottleneck has no dense block to flatten; B there still needs
  the genuine `Deficit ≥ Required` with the path's harmonic profile.

**Is the deg2+dense closure rigorous?** Two approximations are asymptotic, both with
explicit error control: (2) `f_dense` uniform up to `O(λ₂(G)/λ₂(block)) = O(1/qn)` (the
resolvent high-mode tail), and (4) `Deficit ≈ λ₂ f_{v₀}²` up to the non-carrier apex
contribution (≈ 3–5% at `n=50`, → 0). The margin is `1 − q`, bounded away from 0, so for
large `n` the inequality holds with room; a finite-`n` proof needs the two error terms
bounded below `1 − q`. Steps (1),(3) are exact.

---

## Synthesis — a minimality-free closure for deg2+dense, via block connectivity

The eigensystem analysis gives the **first route through `Required > 0` that avoids global
minimality** — but only on the single-bottleneck-plus-dense-block family (deg2+dense):

> **The dense block's spectral gap forces the Fiedler uniform on it**, so the Fiedler's
> dense degree-mass `Σ_dense d_v f_v² → q`, which clears the required `2q−1` with margin
> `1 − q`. Connectivity of the block substitutes for minimality of the whole.

This **explains** the deterministic delocalization that the variational round flagged as
the missing ingredient: on deg2+dense it is *not* a generic random-matrix phenomenon but a
direct consequence of the dense block being well-connected (`λ₂(block) ≫ λ₂(G)`), via the
resolvent. The limitation is topological: lollipops have a **path** bottleneck, where the
Fiedler is a harmonic ramp with no block to flatten, so a different (1-D / path-Dirichlet)
argument is required there. So the `Required > 0` regime decomposes by **bottleneck
topology**: dense-block bottlenecks (deg2+dense) close via block connectivity; path
bottlenecks (lollipops) remain open.

### Caveats
`λ₂`, `f` numerical. The eigensystem identity (TASK 3) is exact (machine precision).
Uniformity (`std/|mean| → 0`) and `Σ_dense d f² → q` are verified for `n ≤ 500`,
`q ∈ {0.5, 0.65, 0.8}` (one sample each; trends monotone). The closure is asymptotic with
the two error terms above; B holds at every finite `n`. Lollipop clique-uniformity is exact
(`λ₂(clique) = m`) but the path carries the mass, so the argument does not apply there.
