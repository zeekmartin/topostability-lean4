# Conjecture B — two-track attack on the `Required > 0` regime

Both tracks aim to convert the **minimality of `λ₂`** (Courant–Fischer) into a proof of the
slack `Deficit − Required = RHS − T ≥ 0` (= B). Code:
[`conjecture_B_variational_contradiction` run].

**Headline (both negative, with one concrete asset).** TRACK A: for `g = f + εp` the
second variation is `R(g) − λ₂ = ε²·pᵀ(L−λ₂)p + O(ε⁴)`, which is `≥ 0` automatically by
minimality. But for **none** of the constructed competitors `p` does `pᵀ(L−λ₂)p` equal a
*constant* multiple of the slack: the ratio `E_p/slack` varies by orders of magnitude with
`n` (smoothing grows `37→222`; degree/inverse-degree shrink to `~0.01`). So the slack is
**not** a second variation of any natural perturbation — minimality-via-explicit-competitor
does not prove B (re-confirming the reverse-vector round). TRACK B: the governing concept is
**eigenvector delocalization** (Laplacian eigenvectors are "no-gaps delocalized"), but the
quantitative results are random-matrix-specific — no citable *deterministic* `fᵀDf ≥ …`
bound. **However, the minimality lemma is already in the repo** (`algebraicConnectivity_le_
rayleigh`, `Shared.lean`), so the Courant–Fischer step of any future variational proof is
formalized — what is missing is the bridge from it to the slack.

---

## TRACK A — second variation of constructed competitors

For `g = f + εp`, `p ⊥ {1,f}`: numerator `= λ₂ + ε²·pᵀLp`, denominator `= 1 + ε²‖p‖²`, so
`R(g) − λ₂ = ε²·(pᵀLp − λ₂‖p‖²) + O(ε⁴) = ε²·pᵀ(L−λ₂)p + O(ε⁴)`. Minimality gives
`pᵀ(L−λ₂)p ≥ 0` (automatic). **A proof needs `pᵀ(L−λ₂)p = c·slack` with constant `c>0`**
(then `slack ≥ 0`). Testing the three competitors:

| graph | `n` | `slack` | `E_p/slack` (a smooth) | (b deg-rw) | (c `D⁻¹f`) |
|---|---|---|---|---|---|
| deg2+dense | 100 | 0.926 | **37.2** | 0.035 | 0.029 |
| deg2+dense | 200 | 0.841 | **73.1** | 0.020 | 0.019 |
| deg2+dense | 500 | 0.744 | **222.1** | 0.009 | 0.008 |
| lollipop | 60 | 0.103 | 8.4 | 0.028 | ~0 |
| lollipop | 105 | 0.090 | 9.9 | 0.009 | ~0 |
| lollipop (short) | 50 | 0.280 | 5.8 | 0.006 | 0.002 |

- **(a) smoothed Fiedler** (move `v₀`'s mass to its neighbours): `E_p ≫ slack` and **grows
  like `n`** (37 → 222). The localized smoothing direction has large `L`-energy; its second
  variation badly over-shoots the slack and is nowhere near proportional.
- **(b) degree-reweighted** and **(c) `D⁻¹f`** (`g_v = f_v(1−ελ₂/d_v)`): `E_p ≪ slack`
  (`~0.01–0.03×`) and **shrinking**. These directions are too "flat" — tiny second
  variation, far below the slack.
- **No competitor gives a constant ratio.** The slack is not `c·pᵀ(L−λ₂)p` for any of `a,b,c`
  (ratios span `0.008` to `222`). Minimality along these directions yields no bound on the
  slack.

**Why it fails (structural).** `slack = fᵀMf − λ₂S²/m`, `M = λ₂Q − L_t` (a fixed quadratic
form in the Fiedler `f`). A second variation `pᵀ(L−λ₂)p` with `p = P̃f` (a linear image of
`f`) is `fᵀ(P̃ᵀ(L−λ₂)P̃)f` — a *different* fixed quadratic form. Matching it to the
`M`-form for a natural `P̃` is exactly what the reverse-vector round showed impossible; the
new smoothing/degree competitors do not change that.

## TRACK B — literature & Mathlib

**Literature.** The relevant concept is **eigenvector delocalization**: Laplacian
eigenvectors are "no-gaps / no-structure delocalized" — the mass cannot concentrate, the
largest entry is small, any large vertex set carries substantial energy
([Braess paradox & delocalization, arXiv:1504.07669](https://arxiv.org/abs/1504.07669);
[eigenvalue gaps of random-graph Laplacians, arXiv:2501.00234](https://arxiv.org/html/2501.00234)).
This is *exactly* the kind of statement that would lower-bound `Σ_{v≠v₀} d_v f_v²` (our open
deg2+dense ingredient). **But all quantitative delocalization bounds are random-matrix /
random-graph results** — high-probability over an ensemble — not deterministic bounds for a
fixed irregular `G`. The deterministic Fiedler literature (nodal domains, Dirichlet
eigenvalues of nodal domains, de Abreu's survey) gives structural facts but **no
`fᵀDf ≥ …` or second-moment lower bound**. No off-the-shelf citable result.

**Mathlib / repo.** The constrained Courant–Fischer *minimality* direction is **already
formalized in this repo**: `Topostability.algebraicConnectivity_le_rayleigh` (`Shared.lean`)
states `algebraicConnectivity G ≤ xᵀLx/‖x‖²` for every `x ≠ 0` with `x ⊥ 1`. So the
ingredient TRACK A would need — "`R(g) ≥ λ₂` for any competitor `g ⊥ 1`" — is available off
the shelf. Mathlib itself has `ContinuousLinearMap.rayleighQuotient` and global
`IsSymmetric.hasEigenvalue_iInf/iSup` (only the *global* extreme eigenvalues), but **no**
constrained min–max / `IsMinOn` for the `k`-th eigenvalue. So the formalizable minimality is
the repo's lemma; what is missing is purely the *mathematical* bridge to the slack.

---

## Synthesis

- **TRACK A is closed:** the slack `Deficit − Required` is not the second variation of any
  natural competitor (smoothing, degree-reweight, inverse-degree). Minimality along an
  explicit direction cannot prove B — the slack is `fᵀMf − λ₂S²/m`, a quadratic in `f` that
  no `pᵀ(L−λ₂)p` reproduces. This matches every prior perturbation attempt.
- **TRACK B is half-positive:** the *concept* needed is **eigenvector delocalization**
  (a lower bound on `Σ_{v≠v₀} d_v f_v²` / the Fiedler's dense second moment), which is the
  precise open ingredient from the scalar-reduction round. The literature confirms it as a
  real phenomenon but supplies only random-matrix bounds; no deterministic citable result.
  The **minimality lemma is already in the repo** (`algebraicConnectivity_le_rayleigh`).
- **Net:** the missing step is a *deterministic, global* use of minimality — not via a
  single competitor (TRACK A rules that out) — that yields a **lower bound on the Fiedler's
  dense second moment** `Σ_{v≠v₀} d_v f_v² ≥ 2q−1` (deg2+dense) or, generally, that the
  Fiedler delocalizes onto the high-degree bulk. That is the one analytic fact on which the
  whole `Required > 0` regime now rests.

### Caveats
`λ₂`, `f` numerical; deg2+dense (q=0.65, n≤500) and lollipops (the only `Required>0`
families). The competitors `a,b,c` are the three constructions specified; `E_p/slack` is
exact per graph. `algebraicConnectivity_le_rayleigh` is a confirmed sorry-free repo lemma.
B (`slack ≥ 0`) holds on every tested graph; no construction converts that into a proof.
