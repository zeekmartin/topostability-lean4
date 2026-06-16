# Conjecture B2′ — reverse-engineering the second-variation test vector

Goal: find an explicit `g ⊥ 1` with `target := C + R″ = gᵀ(L−λ₂)g`, which would
**prove** B2′ (since `gᵀ(L−λ₂)g ≥ 0` on `1⊥`). `target = C + R″ = RHS − W₁ ≥ 0`.
Code: [`conjecture_B_reverse_vector.py`](../conjecture_B_reverse_vector.py).

**Headline (decisive negative).** There is **no constructive test vector**:
1. The **minimum-norm** `g*` with `g*ᵀMg* = target` is, by Lagrange multipliers,
   the **top Laplacian eigenvector** `u_n` (all weight on the largest `μ` minimizes
   `‖g‖²`). It encodes only target's *magnitude*, not its structure — a high-frequency
   mode explained by the 9 low-order degree/Fiedler features at only **R² ≈ 0.51**
   (>0.95 on 11%). Min-norm reverse-engineering is **degenerate**.
2. **No universal `g = Σcₖφₖ`** (polynomial-in-`(D,A)` image of `f`) realizes target
   as a second variation: regressing target on all **45 pairwise energies** of a rich
   9-feature family gives **R² = −0.26** (worse than the mean), and the recovered
   coefficient matrix `Φ` is **indefinite** (3 negative eigenvalues). So `target` is at
   best a *difference* `g₊ᵀMg₊ − g₋ᵀMg₋` — not a single nonnegative certificate.

The constructive-variational route is therefore **closed**. The one positive signal
(the downhill-degree gradient, TASK 3) confirms `C`'s oriented structure but does not
close.

---

## TASK 1 — the minimum-norm vector is degenerate (top Laplacian mode)

`M := L − λ₂I` is PSD on `{1,f}⊥` with eigenpairs `(λᵢ−λ₂, uᵢ)`, `i≥3`. Minimizing
`‖g‖²` subject to `gᵀMg = target` is a Lagrange problem `g = λMg`, so the optimum is
an **eigenvector** of `M`; the *minimum*-norm one puts all weight on the **largest**
`μ = λ_n−λ₂`, i.e. `g* = √(target/(λ_n−λ₂))·u_n`, the **top Laplacian eigenvector**.

This is structurally uninformative — it is the highest-frequency Laplacian mode,
identical in *direction* regardless of what target is. Regressing `g*_v` on the 9
vertex features `{f, d, Df, D²f, Af, A²f, gradf, (d−d̄)f, (d−d̄)²f}`:

> per-graph **R² median 0.51**, mean 0.51, `>0.95` on only **11%** of graphs.

So `g*` is *not* a low-order function of degrees and the Fiedler vector. Conclusion:
"reverse-engineer the minimum-norm vector" cannot reveal a proof pattern — the
canonical min-norm choice discards all of target's structure.

---

## TASK 2 — no universal `g` among polynomial images of `f`

The proof-relevant question: is `target = gᵀ(L−λ₂)g` for some `g = Σcₖφₖ` with
**universal** coefficients `cₖ`, where `φₖ` are the projected feature vectors? Such an
energy equals `cᵀ Φ_graph c` with `Φ_graph,kl = φₖᵀ(L−λ₂)φₗ`, so target must lie in the
span of the pairwise energies `{P_kl}` with a **common, rank-1-PSD** coefficient
pattern. Regressing target on `{P_kl}` over the 9014-graph corpus:

| features | R² | note |
|---|---|---|
| all 45 pairwise energies `P_kl` | **−0.26** | target ∉ span (worse than mean) |
| 9 diagonal energies `φₖᵀMφₖ` only | **−0.84** | single-feature second variations fail |

(The 4-feature version of this regression gave R² = −1.75 in the previous round;
enriching to 9 features improves but stays **negative** — no feasible universal `g`.)

The recovered symmetric coefficient matrix `Φ` is **indefinite**: eigenvalues in
`[−0.28, +2.52]`, **3 negative**. A genuine second-variation certificate needs `Φ ⪰ 0`
(then `g = Φ^{1/2}`-combination). Indefinite `Φ` means the best fit is a **difference
of two energies** `target ≈ g₊ᵀMg₊ − g₋ᵀMg₋`, which is **not** manifestly nonnegative
— it certifies nothing. So even allowing arbitrary signed combinations of these 9
natural directions, `C+R″` is not a Rayleigh-positive form.

---

## TASK 3 — review candidates (cross-check)

| candidate `x` | corr(energy, target) | best `c·E` R² |
|---|---|---|
| `(D+A)f` projected (`= Qf`) | **−0.667** | −3.25 |
| `xᵥ = Σ_{u~v, dᵤ>dᵥ}(fᵥ−fᵤ)` (downhill-degree gradient) | **+0.431** | −1.97 |

- `(D+A)f` **anti-correlates** (−0.67), like the earlier `Df`/`[D,A]f` candidates —
  the signless-Laplacian image of `f` points the wrong way.
- The **downhill-degree gradient** `xᵥ = Σ_{u~v, dᵤ>dᵥ}(fᵥ−fᵤ)` is the **only**
  candidate **positively** correlated with target (+0.43). This is structurally
  natural: it is exactly the per-vertex object dual to `C = Σ(d_h−d_l)f_h(f_h−f_l)`
  (each vertex collects its *uphill-degree* neighbors). It is the most promising
  direction, but its energy still does not match target (R² < 0), so it does not close
  on its own.

---

## Synthesis — the constructive route is closed; what the indefiniteness means

Reverse-engineering confirms and sharpens the previous round: `C+R″ ≥ 0` is **not**
realizable as `gᵀ(L−λ₂)g` for any natural `g` (min-norm is degenerate; no universal
polynomial-in-`(D,A)` image of `f` works; the coefficient matrix is indefinite). A
single-Rayleigh-bound proof does not exist among these vectors.

The **indefinite `Φ`** is the structural lesson: `C+R″` behaves like a *difference* of
second variations, i.e. an **interlacing / two-eigenvalue** quantity, not a single
`λ₂`-Rayleigh gap. This suggests the proof needs either (i) a Courant–Fischer statement
coupling `λ₂` to a *higher* eigenvalue (the `g₋` part), or (ii) the full minimality of
`f` used as a constrained optimum (KKT stationarity `Lf=λ₂f` **plus** the inequality
`gᵀLg ≥ λ₂‖g‖²` applied to a family), rather than a fixed certificate vector. The
oriented **downhill-degree gradient** (+0.43 corr) is the natural building block for the
positive part.

### Caveats
`λ₂`, `f` numerical; all statistics over the 9014 distinct corpus graphs (`n≤9`,
restricted to `λ_n>λ₂`). Min-norm `g*` is exact-by-construction (top eigenvector);
regressions are pooled across graph sizes (correct for a *universal* formula). The
reduction `B ⟸ B2′` remains rigorous; B2′ is unproven. No natural test vector found —
the productive next step is a two-eigenvalue / KKT argument, not another candidate
vector.
