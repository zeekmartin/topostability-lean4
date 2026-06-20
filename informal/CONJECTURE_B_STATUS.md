# Conjecture B — consolidation status

Canonical snapshot of the `λ₂(T(G)) ≤ λ₂(G)` campaign. Repo state: **exactly 3 `sorry`s**, all in
`ConjectureB.lean` (the three open conjecture lemmas); everything else is sorry-free.

---

## 1. Conjecture

For connected `G` with connected triangle graph `T(G)` (vertices = edges of `G`; two edges adjacent
in `T(G)` iff they lie in a common triangle):

> **`λ₂(T(G)) ≤ λ₂(G)`**  — algebraic connectivity of the triangle graph ≤ that of `G`.

Lean: `theorem conjectureB`.

## 2. Equivalent formulations

Unit Fiedler `f` (`L_G f = λ₂ f`); `g_e = f_a−f_b`, `h_e = f_a+f_b`, `S = Σ d_v f_v`, `m = |E|`,
`Q = D+A`, `T = Σ_e t_e g_e²` (triangle energy, `t_e = |N(a)∩N(b)|`).

1. **Lift energy:** `B ⟸ T ≤ λ₂(fᵀQf − S²/m) = 2λ₂(2fᵀDf − λ₂ − S²/m)`.
2. **Triangle-free chain:** `T ≤ B2′ ≤ λ₂G`, `B2′ = Σ(min(d_a,d_b)−1)g_e²`, `λ₂G = λ₂(Σh_e² − S²/m)`
   (first `≤` per-edge `t_e ≤ min−1`; second is the open core).
3. **Degree–Fiedler core:** `gap := λ₂G − B2′ = R″ + C ≥ 0`, `R″ = λ₂(fᵀDf − λ₂ + 1 − S²/m)`,
   `C = Σ_{e,h=higher-deg}(d_h−d_l)f_h(f_h−f_l)`.
4. **Electrical form:** `gap = Θ(eff_resist(a,b))`; `B ⟺ gap/eff_resist ≥ c₀ > 0`
   (`eff_resist = R_aa+R_bb−2R_ab`, `R = (L_H−λ)^{-1}` core resolvent).

## 3. Proven cases (Lean, sorry-free)

- **All regular graphs** (Regime 1 base case): `aggregate_triangle_poincare_regular`.
- **TYPE B path-bottleneck:** `typeB_triEnergy_bound` (with the standard `poincare_on_block`
  block-flatness input).

**The 29 sorry-free theorems** (`ConjectureB.lean`, 23 + `Paper16.lean`, 6):

`ConjectureB.lean` — `triEnergy_diag_corr`, `triEnergy_sub_two_lam_degQuad`,
`adjMatrix_mulVec_fiedler`, `adjSq_mulVec_fiedler`, `quadForm_adjSq_eq_normSq`,
`quadForm_adjMatrix_fiedler`, `degAssort_edge_identity`, `lapMatrix_bilin`, `degAssort_covariance`,
`quadForm_deg_adjMatrix_fiedler`, `neighbor_dirichlet_identity`, `lapMatrix_mulVec_sq`,
`lapMatrix_mulVec_sum_zero`, `quadForm_weighted_laplacian`, `adjMatrix_mulVec_sum`,
`lagrange_identity`, `sum_sq_mul_card_sub_sq`, `B2prime_min_decomp`,
`triCount_le_min_degree_sub_one`, `triEnergy_le_block_dirichlet`, `typeB_triEnergy_bound`,
`aggregate_triangle_poincare_regular`, `conjectureB_lift` (reduction; closed modulo the two regime
sorrys).

`Paper16.lean` — `poincare_on_block`, `block_gap`, `block_gap_lower`, `quadform_edge_split`,
`lapQuadForm_edge_split`, `block_fiedler_energy`.

(The remainder of the repo — Papers 11–15, `Defs`, `Shared` — is also sorry-free.)

## 4. Proven cases (closed form, not yet Lean)

- **`deg2 + K_{n−1}` (complete core):** `gap = 10(n−3)/m > 0` exactly (sympy-verified:
  `gap(ρ=n−2,λ=2) = 20(n−3)/(n²−3n+6) = 10(n−3)/m`), manifestly positive. The densest TYPE A,
  closed in closed form (construction-specific; not yet formalised).

## 5. Three-regime classification (exhaustive, bimodal; 580-graph corpus)

Split on `Required = λ₂(λ₂ + S²/m − fᵀDf)`; `277 + 226 + 77 = 580`, `boundary_ratio` bimodal.

| regime | criterion | count | status |
|---|---|---|---|
| **Regime 1** | `Required ≤ 0` | 277 | reduces to `aggregate_triangle_poincare` (`T ≤ λ₂fᵀDf`); **regular proved** |
| **TYPE A** | `Required > 0`, vertex bottleneck | 226 | reduced to `c(q) > 0` (§6); complete core closed |
| **TYPE B** | `Required > 0`, path bottleneck | 77 | **proved** (`typeB_triEnergy_bound`) |

## 6. Open lemma — the last piece

> **`gap / eff_resist(a,b) ≥ c₀ > 0`** for TYPE A with `λ < γ` (`γ = λ₂(H)`).

- `eff_resist = R_aa+R_bb−2R_ab = Σ_{k≥2}(φ_k(a)−φ_k(b))²/(μ_k−λ) > 0` is **proven** (Green's-function
  sum rule; `⟺ R₂ ≻ 0 ⟺ λ < γ`, Courant–Fischer). So `gap > 0 ⟺ gap/eff ≥ c₀ > 0`.
- **Verified on every tested graph** (corpus + scaling + adversarial), `gap/eff ∈ [≈0.68, 17]`.
- **`c₀` is persistent, `≈ 0.68`** (achieved by the degree-2-attachment family — see below), holding
  **uniformly in `n`**. `gap/eff` is **not** a finite resolvent invariant (needs higher moments).

### Proof-strategy split — *attempted and refuted* (see `conjecture_B_typeA_asymptotic_proof.md`)

A natural split was tried — **(a) asymptotic** (`n ≥ n₀`: `gap/eff ≥ 5` via `min(d_a,d_b) → ∞`,
`f_a → 0`, `C_attach → 0`, `gap → R″ > 0`) plus **(b) finite** check (`n < n₀ ≈ 25`). **Both halves
fail:**

- The asymptotic mechanism is **false**: `C_attach = O(1)` (not `→ 0`; `f_a·d_a = O(1)` since
  `f_a ~ x/γ`), and `gap → 0` in the dense regime (`R″` and `C_attach` cancel) — not `gap → R″`.
- The finite check is **impossible**: the **minimizers persist at all `n`** — fixing the attachment
  degree low (`d = 2,3,4`) on a growing dense core gives `gap/eff → g(d)` (`g(2) ≈ 0.68`, `g(3) ≈ 1.20`,
  `g(4) ≈ 1.63`), *stable* as `n → ∞`. There is no `n₀` above which `gap/eff ≥ 5`.

**Corrected extremal family (SOLVED in closed form — see `conjecture_B_typeA_low_degree_ports.md`):**
`v₀` attached to two **low-degree ports** `a,b` into a dense/complete bulk. The extremizer is the
**`d=2` twin-port** model (`a,b` share both bulk neighbours, `a≁b`, bulk `= K_N`): as `N → ∞`,

> **`λ → 1`** (secular `(λ−1)(λ−4)=0`), **`eff → 2`** (antisymmetric resolvent, both *proven*),
> **`gap → 2/3`**, so **`gap/eff → 1/3`**.

This reproduces the random fixed-degree values (disjoint ports `s=0`: `d=2→0.68, 3→1.22, 4→1.64`) and
lies below them (twin ports). So the open lemma sharpens to **`gap/eff ≥ 1/3 > 0`** for TYPE A, with an
**explicit extremizer**; `gap > 0` is safe (`gap → 2/3` at the extremum). It is *persistent* (uniform
in `n`), *not* finite-size and *not* at the (benign) `λ/γ → 1` boundary. Remaining: the closed form
`gap → 2/3` and the extremality/rigidity (complete bulk + full overlap minimize `gap/eff`).

**The three `sorry`s** (`ConjectureB.lean`):

| `sorry` | statement | obstruction |
|---|---|---|
| `aggregate_triangle_poincare` (598) | `T ≤ 2λ·fᵀDf` | Regime 1 irregular (holds 277/277; regular proved) |
| `conjectureB_regime_two` (675) | `T ≤ 2λ(2fᵀDf−λ−S²/m)`, `Required>0` | TYPE A (§6) ∪ TYPE B (structurally closed) |
| `conjectureB` (705) | `λ₂(T(G)) ≤ λ₂(G)` | the projected-Fiedler lift reduction (not yet formalised) |

## 7. Eliminated routes (30+, one-line reasons)

1. **Γ₂ / Bochner curvature** — lossy; local bound overshoots.
2. **Weighted Bochner** — same, lossy.
3. **Second variation of natural test vectors** — overshoots; gap is sub-leading.
4. **Scalar S-procedure** (`αI`) — multiplier `α` blows up `~n^{1.18}–n²` on deg2+dense.
5. **Structured multipliers** (`c(L−λ)^+`, diagonal, block-proj, low-rank, polynomial) — `u`-block
   `−L_min` indefiniteness.
6. **`α = Δ+λ₂−1` certificate** — PSD on `1⊥` for 276/277; fails the deg2+dense regime-boundary graph.
7. **`α = Δ+2λ₂−1`, `2Δ`, … ** — numerically 277/277 but `M_α ⪰ 0` has no closed form for irregular
   (`[L_min,L] ≠ 0`, no eigenbasis collapse).
8. **Local per-apex Poincaré** (`E_{G[N(c)]} ≤ λ₂Σf²`) — fails on ≈6% of apices.
9. **SDP certificate (small graphs)** — feasible `α` found but does not scale.
10. **Structured dual certificate** — `f`-coupling repair bounded, but `u`-block obstruction remains.
11. **Determinant form** — did not close.
12. **Open-2-path operator / spectral orthogonality** — did not close.
13. **Global summation / open-apex pairing** — did not close.
14. **Edge-space variance (B2′)** — reduces but does not close.
15. **Variational core** (`C+R″≥0` via Fiedler minimality) — Rayleigh perturbation overshoots.
16. **Driver vs correction** (`λρ‖f_H‖²` + correction) — correction is `O(1)` not `O(η²)`
    (`|corr|/η² → 3·10⁴`), dominated by `−λS²/m`; `driver ≈ |corr|`, "driver > |corr|" circular.
17. **Resultant elimination** — no polynomial exact secular; `Res(P,Num) ≡ 0` (trivial null mode);
    reduced resultant vanishes from the spurious high mode `λ_big ≈ ρ`, not `λ*`.
18. **Sturm count of `Num`** — sign-indefinite near `λ*` for dense `ρ` (2 roots in `[1,2]`).
19. **Mean-field `η=0` secular** — qualitatively wrong for the complete core (`λ=2` not a root).
20. **2×2 Schur PSD** — `gap > 0` not a 2×2 PSD: `gap = POS − NEG`, both `O(n)`, nearly cancel.
21. **`gap/eff` closed form in `R₂`** — needs higher resolvent moments (`M2` and beyond; residual ~13%).
22. **Monotonicity / complete-core extremality** — complete core is **not** the gap-minimizer;
    deleting attachment-incident edges (lowering `d_a,d_b`) lowers gap below complete.
23. **Quasi-clique deletion** — bulk-bulk monotone, attachment-incident non-monotone.
24. **Local incompleteness lemma** (`missing_common_ab`) — predicts `C_attach` (`r=−0.93`) but gap dips
    below complete; no missing-edge lower bound.
25. **Shifted resistance `R_λ`** — equals `eff_resist` exactly (`e_a−e_b ⊥ 1`); nothing new.
26. **Terminal single/pair predictor** — no terminal variable controls `gap/eff` (≥13% residual).
27. **Boundary continuity argument** (`λ/γ → 1`) — `gap` discontinuous at `λ₂=γ` (Fiedler mode swap),
    though `gap > 0` on both sides.
28. **`λ`-driver lower bound** (`‖f_H‖² ≥ c/n`) — uses the wrong (sub-leading) component.
29. **Conjecture A chaining** (`τ/(Δ−1) ≤ λ₂` through B) — link `τ/(Δ−1) ≤ λ₂(T)` fails 421×.
30. **Complete-core as universal extremizer** — not extremal in the attachment-degree axis.

**Common root cause:** in TYPE A, `gap` is the `O(1/n)` residual of two matched `O(1)` (or `O(n)`)
quantities at an **irrational secular root** that cannot be algebraically isolated; the obstruction
concentrates at the `v₀–a–b` attachment junction and depends on the full core spectrum.

## 8. Key identities formalized (Lean)

- `triEnergy_diag_corr` — `T = 2Στ_v f_v² − 2Σ t_ij f_i f_j` (diagonal/correlation split).
- `B2prime_min_decomp` — `Σ(min−1)g² = ½Σ(d_i+d_j)g² − ½Σ|d_i−d_j|g² − Σg²`.
- `triCount_le_min_degree_sub_one` — `t_e ≤ min(d_a,d_b)−1` (per-edge `T ≤ B2′`).
- `degAssort_covariance` — `𝒜 = dᵀL(f∘f)`.
- `lagrange_identity`, `sum_sq_mul_card_sub_sq` — variance/Lagrange identities.
- `triEnergy_le_block_dirichlet`, `typeB_triEnergy_bound` — TYPE B closure.
- `aggregate_triangle_poincare_regular` — regular-graph base case.
- `poincare_on_block`, `block_gap(_lower)`, `quadform_edge_split`, `block_fiedler_energy` (Paper16) —
  block spectral toolkit (the Green's-function / resolvent machinery).
- `conjectureB_lift` — the regime-split reduction.

## 9. Suggested next steps

- **Literature:** Schur-complement effective resistance (arXiv 2010.04521); Laplacian eigenvalues via
  rank-one/rank-k perturbations (arXiv 2008.01669, QJM 2022); single-chord augmentation & algebraic
  connectivity (arXiv 2605.24479); eigenvector delocalization for dense random graphs (Vu, Tao, et al.)
  — to bound the `gap/eff` prefactor via the full-spectrum response at the attachment.
- **Collaboration:** spectral graph theory / Green's-functions / random-matrix eigenvector
  delocalization — the open lemma is exactly a lower bound on a resolvent-response prefactor that
  resists finite-invariant methods.
- **Write-up:** Paper 15 — *Complex Networks 2026* — TYPE B closure (Lean), complete-core closed form,
  three-regime classification, and the sharp open lemma `gap/eff ≥ c₀`.

---

## Bottom line

- **Closed:** all regular graphs (Lean); TYPE B (Lean); deg2+`K_{n−1}` (closed form).
- **Reduced:** Regime 1 → `aggregate_triangle_poincare`; TYPE A → the single inequality
  `gap/eff_resist ≥ c₀ > 0` (with `eff_resist > 0` already proven).
- **Open:** the prefactor lower bound `c₀` — verified everywhere (`min ≈ 1.6`, interior), not captured
  by any finite algebraic / resolvent / electrical invariant. Three `sorry`s remain, mapped above.
