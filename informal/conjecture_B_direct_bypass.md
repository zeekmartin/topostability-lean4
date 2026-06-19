# Conjecture B — direct lift target vs aggregate Poincaré, and the covariance in the literature

Two equivalent reformulations of the lift bound (`f` unit Fiedler, `S = Σ_v d_v f_v`, `m = |E|`,
`𝒜 = Cov_L(d,f²) = dᵀL(f∘f) = Σ_{ab∈E}(d_a−d_b)(f_a²−f_b²)`):

| | inequality | meaning |
|---|---|---|
| **direct lift-B** | `T ≤ RHS := λ₂(2fᵀDf − λ₂ − S²/m)` ⟺ `Open ≥ target_B := −𝒜 + λ₂S²/m` | the lift certificate `λ₂(T(G)) ≤ λ₂(G)` |
| **aggregate Poincaré** | `T ≤ λ₂fᵀDf` ⟺ `Open ≥ target_AP := λ₂fᵀAf − 𝒜` (`fᵀAf = fᵀDf − λ₂`) | `aggregate_triangle_poincare` |

(Both via the master identity `T + Open = Σ_v[σ_v−(d_v−λ₂)²]f_v²`; algebra verified, residual
`7·10⁻¹²`.) Their gap is `target_AP − target_B = λ₂(fᵀAf − S²/m) = −Required/1`, `Required =
λ₂(λ₂+S²/m−fᵀDf)`. Code: [`conjecture_B_direct_bypass.py`](../conjecture_B_direct_bypass.py), 580
graphs.

> **Note on the ½.** `Cov_L(d,f²)` is the sum over **unordered** edges *without* a ½; the ½ appears
> only for the ordered double sum `½Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)`. (A spurious ½ initially
> produced 3 phantom failures; with the correct normalisation every test below is clean.)

---

## PART 1 — the direct lift target is not a bypass

Both inequalities hold on the whole corpus (consistency `(Open−target_B) = (RHS−T)`, residual
`7·10⁻¹²`):

| test | holds |
|---|---|
| direct lift-B `T ≤ RHS` (≡ `Open ≥ target_B`) | **580/580** |
| aggregate Poincaré `Open ≥ target_AP` | **580/580** |

**Q1 — margin gained by going direct.** `target_AP − target_B = λ₂(fᵀAf − S²/m)` is `≥ 0` only in
regime (i) (`Required ≤ 0`), holding on **277/580**; on the other **303/580** (regime (ii)) it is
**negative — the direct target is *larger*, i.e. harder.** Median relative difference `−0.4%`. So
going direct yields *no systematic margin*: it helps in regime (i), hurts in regime (ii), wash on
median.

**Q2 — when is B trivial (`Open ≥ 0` suffices, `target_B ≤ 0`)?** Only **22/580** (14 corpus, 8
barbell) — exactly the graphs with `𝒜 ≥ λ₂S²/m` (requires `𝒜 > 0`, the rare assortative case;
`𝒜 > 0` on only 76/580). The same 22 have `target_AP ≤ 0`. So **96% of graphs genuinely need
`Open > 0`.**

**Q3 — tightness on the 558 nontrivial graphs.** `Open/target_B`: min **1.0061**, median `1.43`;
`Open/target_AP`: min `1.0171`, median `1.31`. At the worst case the **direct target is slightly
tighter** (1.006 vs 1.017). Tightest direct-B graph: `corpus, n=73, λ₂=1.99, 𝒜=−115.4, S²/m=1.41`,
so `target_B ≈ −𝒜 = 115.4` dominated by the covariance magnitude, `Open ≈ 119` — a `0.6%` margin.

**Q4 — classification.** B needs `Open > 0` on **558/580**; of these 257 are regime (i), 301
regime (ii) (only 2 regime-(ii) graphs are trivial).

**Verdict.** The direct lift target `Open ≥ −𝒜 + λ₂S²/m` is *not* easier than aggregate Poincaré —
marginally tighter at the worst case and harder in regime (ii). When `𝒜 ≪ 0` (hub-flat graphs) it
reduces to `Open ≥ |Cov_L(d,f²)| + λ₂S²/m`, i.e. the open energy must clear the **covariance
magnitude** plus a small spectral correction. **PART 1 does not close B** — the binding object is
still `Cov_L(d,f²)`. Hence PART 2.

---

## PART 2 — `Cov_L(d,f²) = dᵀL(f∘f)` in spectral graph theory

### 2.1 It is the Dirichlet (energy) bilinear form / mutual energy

`⟨u,v⟩_L := uᵀLv = Σ_{ab∈E}(u_a−u_b)(v_a−v_b)` is the **Dirichlet form** `ℰ(u,v)` of the graph —
the standard energy inner product on functions modulo constants (Doyle–Snell, *Random Walks and
Electric Networks*; Lyons–Peres, *Probability on Trees and Networks*). So

> **`Cov_L(d,f²) = ℰ(d, f²)`** — the *mutual energy* of the degree function `d` and the squared
> Fiedler `f²`; equivalently the dissipated power when the "degree potential" drives a current and
> `f²` is the test potential.

In the Gaussian-Markov-random-field reading, `L` is the precision (inverse covariance) operator, so
`uᵀLv` is a precision-weighted pairing; the genuine covariance is `L⁺`, and effective resistance is
`R(a,b) = (e_a−e_b)ᵀL⁺(e_a−e_b)` (Klein–Randić, *resistance distance*). Calling `dᵀLf²` a
"covariance" is precise as the *Dirichlet/energy* pairing, not the `L⁺` covariance.

### 2.2 NEW exact identity: the covariance is a Bakry–Émery carré-du-champ functional

Let `Γ(f)(v) = ½Σ_{u∼v}(f_v−f_u)²` be the **carré du champ** (Bakry & Émery, 1985; the graph version
in Lin–Yau and Bakry–Émery-on-graphs literature). At a Laplacian eigenvector (`Lf = λ₂f`) the
*eigenfunction Bochner identity* holds pointwise (verified, residual `7·10⁻¹⁴`):

> **`L(f²) = 2λ₂·f² − 2·Γ(f)`**  (equivalently `Δ(f²) = 2fΔf + 2Γ(f)` with generator `Δ = −L`).

Degree-averaging gives (verified, residual `3·10⁻¹²`):

> **`Cov_L(d, f²) = 2λ₂·fᵀDf − 2·⟨d, Γ(f)⟩`**,  `⟨d,Γ(f)⟩ = Σ_v d_v·Γ(f)(v)`,

and the un-weighted total is fixed: `Σ_v Γ(f)(v) = fᵀLf = λ₂`. Consequences:

- **Hub-flatness is a curvature statement.** `𝒜 < 0 ⟺ ⟨d, Γ(f)⟩ > λ₂·fᵀDf`: the *degree-weighted
  local Dirichlet energy* exceeds `λ₂` times the degree-weighted mass — a local-energy-over-mass
  (Poincaré/curvature) excess concentrated at hubs. This is exactly the Bakry–Émery `Γ₂ ≥ KΓ`
  flavour (the `Γ`-functional weighted by the reference measure `d`).
- **Target reframed.** `B ⟺ Open ≥ 2⟨d,Γ(f)⟩ − 2λ₂fᵀDf + λ₂S²/m`. The open-2-path energy must
  dominate the *excess degree-weighted carré-du-champ* `2(⟨d,Γ(f)⟩ − λ₂fᵀDf)` up to `λ₂S²/m`.

This places the obstruction inside `Γ`-calculus: a Bochner/`Γ₂` lower bound controlling
`⟨d, Γ(f)⟩` against `λ₂·fᵀDf` would feed directly into B. (This identity is exact and algebraic —
formalisable in the same style as `degAssort_covariance`; left for a later round per scope.)

### 2.3 Cauchy–Schwarz to the degree-irregularity (sigma) index

Since `ℰ(·,·)` is an inner product,

> `|Cov_L(d,f²)| = |ℰ(d,f²)| ≤ √( ℰ(d,d)·ℰ(f²,f²) )`,  `ℰ(d,d) = Σ_{ab∈E}(d_a−d_b)²`.

`ℰ(d,d) = Σ_{ab∈E}(d_a−d_b)²` is the **Gutman sigma index `σ(G)`** (Gutman, Togan, et al.), the
squared-difference graph-irregularity measure (the `ℓ¹` analogue `Σ|d_a−d_b|` is the **Albertson
irregularity**, 1997). So the load-bearing correction is bounded by the graph's degree
irregularity:

> `|𝒜| ≤ √( σ(G)·ℰ(f²,f²) )`.

This ties the hub correction to the irregularity-index literature; on regular graphs `σ(G)=0 ⟹
𝒜=0` (the correction vanishes, recovering the regular-case proof). The bound is loose (it ignores
the Fiedler/degree alignment) but it is the natural a-priori control.

### 2.4 Degree variance, Grone–Merris, and `λ₂`

`σ(G)/2m` is the edge-degree variance; classical Laplacian-spectrum/degree links — Grone–Merris–Bai
(majorisation of the Laplacian spectrum by the conjugate degree sequence), Brouwer's conjecture
(partial-sums of eigenvalues vs edges + binomials), and the bounds `λ₂ ≤ (n/(n−1))·δ`,
`λ_max ≥ Δ+1` — bound the *spectrum* by degree data. They constrain `λ₂` and the degree spread but
do **not** give the *signed, Fiedler-aligned* pairing `ℰ(d,f²)`; the needed input is the
alignment between `d` and `f²` (hub-flatness), which these inequalities do not encode.

### 2.5 Normalised Laplacian, effective resistance, free energy (weaker links)

- **Chung normalised Laplacian** `𝓛 = I − D^{-1/2}AD^{-1/2}`: recasts `d` as the stationary measure;
  the corresponding Dirichlet form is `Σ_{ab}(g_a/√d_a − g_b/√d_b)²`. `Cov_L(d,f²)` is in the
  *combinatorial* form; the prior `D4` round (`conjecture_B_rho_lemmas.md`) found the normalised gap
  `μ₂` the right *scale* but not a closing bound — consistent with the alignment, not the scale,
  being the issue.
- **Effective resistance / mutual energy** (§2.1): `ℰ(d,f²)` is a current–potential pairing; no
  closed resistance formula because `d` is generally **not** in `range(L)` (so it is not a single
  current's potential).
- **Graph free energy / GFF.** With `L` the GFF precision and `f²` a density, `ℰ(d,f²)` is a
  cross-energy gradient term; this is suggestive (Dirichlet-energy/entropy duality) but yields no
  concrete inequality here.

## Conclusion

- **PART 1:** the "direct" lift target `Open ≥ −Cov_L(d,f²) + λ₂S²/m` is *not* a bypass — it is
  marginally tighter than aggregate Poincaré at the worst case and harder in regime (ii); B needs
  `Open > 0` on 558/580 graphs; the binding object remains `Cov_L(d,f²)`.
- **PART 2 (the real lever):** `Cov_L(d,f²) = ℰ(d,f²)` is the Dirichlet mutual-energy form, and the
  **new exact identity `Cov_L(d,f²) = 2λ₂fᵀDf − 2⟨d,Γ(f)⟩`** places it squarely in **Bakry–Émery
  `Γ`-calculus**: hub-flatness `=` a degree-weighted local-energy-over-mass excess. The natural
  attack is a Bochner/`Γ₂` bound on `⟨d,Γ(f)⟩` vs `λ₂fᵀDf`; the a-priori control is Cauchy–Schwarz
  to the **Gutman sigma index** `σ(G)=Σ_{ab}(d_a−d_b)²`. Standard spectral–degree theorems
  (Grone–Merris–Bai, Brouwer, `λ₂≤(n/(n−1))δ`) bound the spectrum and degree spread but miss the
  `d`–`f²` *alignment* that hub-flatness encodes.

**Most promising next step:** a graph Bakry–Émery / Bochner argument for `⟨d,Γ(f)⟩ ≤ λ₂fᵀDf +
½(Open + λ₂S²/m)` — i.e. curvature controls the degree-weighted carré du champ.
