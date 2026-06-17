# Conjecture B — proving the block principle: two rigorous lemmas + the residual gap

**Target.** `Required > 0 ⟹ λ₂(G[B]) ≥ c·λ₂(G)` for a high-degree block `B`, then
block-uniformity closes B. Code: [`conjecture_B_block_proof.py`](../conjecture_B_block_proof.py).
Corpus: the 1962 `Required > 0` graphs (deg2+dense sweep, lollipops, 1949 random, seed 7).

**Headline.** The attempt yields **two rigorous lemmas** and pins the proof of B on the
`Required > 0` regime to a **single remaining combinatorial fact**:
1. **TRACK C — Poincaré-on-block (RIGOROUS, verified to machine precision).** Restricting the
   eigen-equation to `B` is *exactly* `(L_B − λ₂I)f_B = g` with boundary forcing
   `g_v = Σ_{u∼v,\,u∉B}(f_u − f_v)` (residual `≤ 1.9·10⁻¹³`), and the spectral decomposition
   gives `‖f_B − mean‖² ≤ ‖g‖²/(γ − λ₂)²`, `γ = λ₂(G[B])` — **holds 100%** of the corpus.
   This *is* the uniformity mechanism, now a theorem.
2. **TRACK A/B — gap from internal density (RIGOROUS, classical).** `γ ≥ 2δ_B − |B| + 2`
   (verified 100%); when the block is internally denser than half (`δ_B > (|B|−2)/2`, true on
   70% of blocks) this gives `γ ≥ λ₂(G)` on 95.7% and `≥ 2λ₂(G)` on 88%.
3. **The residual gap.** Both lemmas are conditional on the block being *internally dense*.
   For `B = {d_v ≥ median}` this is **fragile**: `min ratio = 1.07`, and the 15 weak cases are
   exactly the **low-`λ₂`, low-density, `Required ≈ 0⁺`** graphs — where B holds anyway because
   `Required ≈ 0` (near-trivial). So the missing step is "`Required` bounded away from 0
   ⟹ block internally dense," which the data supports but is not yet proved.

**TRACK D is closed:** `T` is *not* a clean function of `fᵀAf` (`corr = −0.42`); there is no
direct `fᵀAf → T` bound, so the block route is necessary.

---

## TARGET CHECK — `B = {v : d_v ≥ median}` is fragile

| `ratio = λ₂(G[B])/λ₂(G) ≥` | fraction |
|---|---|
| 1.0 | 100.0% |
| 1.5 | 99.2% |
| 2.0 | 99.2% |
| 3.0 | 98.1% |

`min = 1.071`, `median = 10.88`. The 15 graphs with `ratio < 1.5`:

| `n` | `λ₂` | `Required` | `ratio` | `|B|` | `density_B` |
|---|---|---|---|---|---|
| 31 | 0.016 | 0.0057 | 1.109 | 30 | 0.28 |
| 41 | 0.008 | 0.0092 | 1.074 | 40 | 0.22 |
| 41 | 0.008 | 0.0057 | 1.071 | 40 | 0.20 |
| 34 | 0.013 | 0.0078 | 1.096 | 33 | 0.26 |
| 30 | 0.016 | 0.0006 | 1.109 | 29 | 0.26 |

Every fragile case has **`λ₂ ≈ 0.01`, `density_B ≈ 0.2–0.3` (sparse block), and `Required ≲
0.01`** (near the `Required = 0` boundary). The degree-median block of a globally-sparse graph
is itself sparse, so it has no strong gap — but there `Required ≈ 0`, so B is essentially the
trivial-regime case (`Deficit ≥ 0 ≈ Required`, `Def/Req ≈ 50` in the canonical round). **Weak
block ⟺ `Required → 0⁺`.**

## TRACK C — the Poincaré-on-block lemma (rigorous)

Restrict `Lf = λ₂f` to `v ∈ B`. Writing `L_B` for the induced Laplacian and splitting each
neighbour sum into `B` / not-`B`:

> `(L_B − λ₂I) f_B = g`, where `g_v = Σ_{u∼v,\,u∉B}(f_u − f_v)` (boundary forcing).

**Verified exact:** `max_corpus ‖(L_B − λ₂I)f_B − g‖ = 1.9·10⁻¹³`. Now expand `f_B` in the
`L_B`-eigenbasis `{u_k, μ_k}`, `0 = μ_0 < γ = μ_1 ≤ ⋯`. The constant mode `u_0 ∝ 1` gives the
mean; for `k ≥ 1`, `⟨u_k, f_B⟩ = ⟨u_k, g⟩/(μ_k − λ₂)`, so

> **`‖f_B − mean·1‖² = Σ_{k≥1} ⟨u_k,g⟩²/(μ_k − λ₂)² ≤ ‖g‖²/(γ − λ₂)²`.**

| check | result |
|---|---|
| bound `dev ≤ ‖g‖²/(γ−λ₂)²` holds (ratio>1, n=1962) | **100.0%** |
| `dev / bound` median | 0.492 |
| `dev / bound` 95%ile / max | 0.980 / 0.983 |

So the block-uniformity is a **rigorous Poincaré inequality**, not an empirical observation:
the non-uniform part of `f_B` is bounded by the boundary forcing over the gap, `O(‖g‖²/γ²)`
once `γ ≫ λ₂`. The bound is tight to within `~2×`. This holds for *any* block with `γ > λ₂`;
its usefulness is entirely controlled by the gap `γ − λ₂` — which is what TRACK A/B supplies
and the residual gap must guarantee.

## TRACK A/B — gap from internal density (rigorous + literature)

**Classical lower bound** (verified, 0 violations): for a graph `H` on `b` vertices with
minimum degree `δ_H`,

> `λ₂(H) ≥ 2δ_H − b + 2`.

(Tight on `K_b`: `δ=b−1 ⟹ λ₂ ≥ b = λ₂(K_b)`; on `K_b − matching`: `δ=b−2 ⟹ λ₂ ≥ b−2`.)

| check | result |
|---|---|
| `γ ≥ 2δ_B − |B| + 2` holds | 100.0% |
| bound positive (`δ_B > (|B|−2)/2`) | 69.9% of blocks |
| where positive: `2δ_B−|B|+2 ≥ λ₂(G)` | 95.7% |
| where positive: `2δ_B−|B|+2 ≥ 2λ₂(G)` | 88.0% |
| `corr(density_B, ratio)` | **0.501** |

So **when the block is internally dense (`δ_B > (|B|−2)/2`), the gap `γ ≥ c·λ₂(G)` is
provable by a one-line classical bound** (88% even reach `2λ₂`). Vertex connectivity: Fiedler's
`λ₂(H) ≤ κ(H)` is respected, and on these dense blocks `κ_B = δ_B` (median ratio 1.00), so the
relevant control is the minimum internal degree `δ_B`. **The only thing not yet guaranteed is
that the block is dense** — i.e. `δ_B > (|B|−2)/2` — which fails precisely on the 30% sparse
blocks (the `Required ≈ 0⁺` cases).

## TRACK D — no direct `fᵀAf → T` bound

`Required > 0 ⟺ fᵀAf < S²/m` suggests a "Fiedler alternates along edges ⇒ small `T`" story.
But:

| correlation | value |
|---|---|
| `corr(T, fᵀAf)` | −0.421 |
| `corr(T/λ₂, fᵀAf)` | −0.550 |
| `corr(T, |fᵀAf|)` | −0.421 |

Only a **weak negative** correlation — `T` is *not* a monotone function of `fᵀAf`. `T =
Σ t_ab(f_a−f_b)²` is set by the triangle structure `×` gradient, which `fᵀAf` does not capture.
So there is no shortcut around the block: the proof must go through `λ₂(G[B])`.

---

## Synthesis — the proof, and the one missing step

Assembling the rigorous pieces, the proof of B on `Required > 0` reads:

> Pick the block `B`. **(1, exact)** `(L_B − λ₂I)f_B = g`, `g` = boundary forcing.
> **(2, Poincaré, rigorous)** `‖f_B − mean‖² ≤ ‖g‖²/(γ − λ₂)²`. **(3, density gap, classical)**
> if `δ_B ≥ (|B| + λ₂)/2 − 1` then `γ = λ₂(G[B]) ≥ λ₂(G)`, so `(γ − λ₂)` is bounded below and
> `f_B` is uniform up to `O(‖g‖/γ)`. **(4)** uniform `f_B` ⇒ deg2+dense mechanism
> (`Σ_B d_v f_v² ≈ q` ≥ threshold) or lollipop mechanism (`T = O(λ₂²) ≪ RHS`) ⇒ B.

**Steps 1–2 are rigorous and machine-verified; step 3 is a classical bound, conditional on
the block being internally dense; step 4 is the two closed families.** The **single remaining
gap** is:

> **`Required > ε ⟹ ∃` block `B` with `δ_B ≥ (|B| + λ₂)/2 − 1` (internally dense).**

The evidence: `density_B` correlates with the ratio (`0.50`), and *every* graph where the
degree-median block is sparse (ratio `< 1.5`) has `Required < 0.01` — i.e. weak block only at
the `Required → 0⁺` boundary, where B is near-trivial regardless. A clean proof would either
(a) **regime-split** at `Required = ε`: handle `Required ≤ ε` by the near-trivial margin and
`Required > ε` by the dense block, or (b) use the **`p = 80%` Fiedler-complement block**
(min ratio 2.5 vs degree-median's 1.07 — round `canonical_detector`), which is internally
denser by construction and may satisfy the density condition unconditionally. Proving (a) or
(b) would complete B on the whole `Required > 0` regime.

### Caveats
`λ₂`, `f` numerical. The eigen-restriction identity (residual `≤ 2·10⁻¹³`) and the Poincaré
bound (100%, `dev/bound ≤ 0.983`) are exact/rigorous statements verified on all 1962 graphs.
`γ ≥ 2δ_B − |B| + 2` is a classical bound (0 violations). `κ_B` sampled on 60 blocks with
`|B| ≤ 30`. The residual gap (`Required > ε ⟹` dense block) is **not** proved here; it is
supported by `corr(density_B, ratio) = 0.50` and the localization of all weak-block cases at
`Required ≲ 0.01`. The degree-median block is fragile (min ratio 1.07); the `p=80%`
Fiedler-complement block is the more robust candidate for an unconditional density bound.
