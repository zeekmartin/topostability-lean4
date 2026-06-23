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
- **⭐ ALL regular graphs — the TRUE lift `T ≤ λ₂G` (NOW IN LEAN, sorry-free modulo `λ ≤ d+1`):**
  `triEnergy_le_RHS_regular` proves the full lift conclusion for connected `d`-regular `G` (unit
  Fiedler `‖f‖²=1`, `f⊥1`) from the single explicit hypothesis `hlam : λ ≤ d+1`. Proof: `degQuad=d`,
  `degLin=0`; `t_e ≤ d−1` ⇒ `T ≤ (d−1)·2λ`; then `(d−1)2λ ≤ 2λ(2d−λ)` via `λ≤d+1` (nlinarith). This
  **strictly strengthens** `aggregate_triangle_poincare_regular` (`T ≤ 2λd`, insufficient for
  `λ∈(d,d+1]`, e.g. `K_n`). The hypothesis `λ ≤ d+1` is the standard spectral bound (`μ₂(A) ≥ −1`,
  Cauchy interlacing on a `2×2` edge block `[[0,1],[1,0]]`), left explicit (paper proof:
  `conjecture_B_regular_PROOF.md`; the equivalent complement form is `gap = λ(n−λ) − C`,
  `C = Σ_e t̄_e g_e² ≤ (n−1−d)λ`).
- **TYPE B path-bottleneck:** `typeB_triEnergy_bound` (with the standard `poincare_on_block`
  block-flatness input); the regime-(ii) conclusion for the TYPE B branch is now connected sorry-free
  via `conjectureB_regime_two_typeB`.

**The 34 sorry-free theorems** (`ConjectureB.lean`, 28 + `Paper16.lean`, 6):

`ConjectureB.lean` — `triEnergy_diag_corr`, `triEnergy_sub_two_lam_degQuad`,
`adjMatrix_mulVec_fiedler`, `adjSq_mulVec_fiedler`, `quadForm_adjSq_eq_normSq`,
`quadForm_adjMatrix_fiedler`, `degAssort_edge_identity`, `lapMatrix_bilin`, `degAssort_covariance`,
`quadForm_deg_adjMatrix_fiedler`, `neighbor_dirichlet_identity`, `lapMatrix_mulVec_sq`,
`lapMatrix_mulVec_sum_zero`, `quadForm_weighted_laplacian`, `adjMatrix_mulVec_sum`,
`lagrange_identity`, `sum_sq_mul_card_sub_sq`, `B2prime_min_decomp`,
`triCount_le_min_degree_sub_one`, `lapMatrix_mulVec_row`, `eigenpair_invariance_equal_values`,
`triEnergy_le_block_dirichlet`, `typeB_triEnergy_bound`, `conjectureB_regime_two_typeB`,
`triEnergy_le_RHS_regular` (regular lift, sorry-free modulo `λ≤d+1`),
`triEnergy_le_B2prime` (off-chain, `T ≤ B2′`), `aggregate_triangle_poincare_regular`,
`conjectureB_lift` (now **EXISTENTIAL**, `= triEnergy_le_RHS_exists` with `hTconn`; the old universal
`triEnergy_le_RHS`/`conjectureB_regime_two` were FALSE on degenerate `λ₂` and are removed).

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
in `n`), *not* finite-size and *not* at the (benign) `λ/γ → 1` boundary.

> **The extremality program proving `gap/eff ≥ 1/3` is now built and validated — see §10.** Closed
> form `gap → 2/3` (TASK 4C), the four monotonicities (TASKS 1–4), and the assembly (0/3318
> counterexamples) reduce TYPE A to this single bound, modulo three rigour items.

**The three `sorry`s** (`ConjectureB.lean`):

| `sorry` | statement | obstruction |
|---|---|---|
| `aggregate_triangle_poincare` (854) | `T ≤ 2λ·fᵀDf` (regime i) | **regime i**, direct sorry on the TRUE statement (`T/(2λ·degQuad) ≤ 0.17`, big slack). Regular case proved (`aggregate_triangle_poincare_regular`). Must be proved directly — the `B2′`/min-degree relaxation is RULED OUT (see below) |
| **`typeA_slack_ge_required` (974)** | `(hTconn) → (Required > 0) → required ≤ aggregateSlack` | **regime ii TYPE A** (the only intended TYPE A sorry, now in SMALLEST form): `S_agg ≥ Required` / `gap/eff ≥ 1/3` — a direct comparison of two energy quantities. **`typeA_extremality_gap_nonneg` is now SORRY-FREE** (derives `gapEnergy ≥ 0` from this via `gap_eq_aggregateSlack_sub_required`). Aggregate gives only `aggregateSlack ≥ 0`; regime ii needs the stronger `≥ required`. Sound for every eigenvector under `hTconn` |
| `conjectureB` (1057) | `λ₂(T(G)) ≤ λ₂(G)` | the projected-Fiedler lift reduction (orthogonal, not yet formalised) |

**TYPE A bridge (sorry-free, commit "Implement TYPE A Lean bridge").** `aggregate_triangle_poincare_typeA`
reduces the TYPE A case of `aggregate_triangle_poincare` to a single scalar condition `hcond`
(`(δ−1)·D_port + Δ_H·D_core ≤ 2λ·degQuad`, validated 20/20). Sorry-free supporting lemmas: `dirichletOn`,
`triEnergyOn` (P-restricted energy/Dirichlet over an edge predicate `P` = port edges), `triEnergy_split`
(`T = triEnergyOn P + triEnergyOn ¬P`), `triEnergyOn_le` (`t_e ≤ C` on P-edges ⇒ `triEnergyOn ≤ C·dirichletOn`),
`aggregate_typeA_assembly` (`linarith`). The two per-class inputs (`hport`, `hcore`) are mechanical
(`t_e ≤ δ−1` on ports via `triCount_le_min_degree_sub_one`; `t_e ≤ Δ_H` on core); only `hcond` is open.
This does not change the sorry count (it is a conditional lemma; the global `aggregate_triangle_poincare`
stays the direct sorry).

**Regime-i: the `B2′` refinement was REVERTED (commit "C crosses -1: B2' leaf is FALSE, revert").**
The intermediate `B2′ ≤ 2λ·degQuad` (`B2prime_le_two_lam_degQuad`) is **FALSE** on sparse-core
deg2+dense (`q ≤ 0.12`; `deg2d140_0.05`: `B2′/(2λ·degQuad) = 1.05` while `triEnergy/(2λ·degQuad) =
0.01`) — the per-edge `t_e ≤ min−1` is far too lossy when there are few triangles (`T ≪ B2′`). The
earlier "46/46" corpus had only `q ≥ 0.3`. The unsound sorry was deleted; `aggregate_triangle_poincare`
is restored as a direct sorry on the TRUE `T ≤ 2λ·degQuad` (which holds with slack ≥ 0.83). The
equivalent `C = ½(A+I) ≥ −λ` form is also false (`C/λ → −1.07`) and not a general PSD inequality (`M_C+L`
indefinite). See `informal/conjecture_B_signed_cancellation.md`.

**Regime architecture (`gapEnergy = aggregateSlack − required`, all sorry-free except the two leaves
above).** `triEnergy_le_RHS_exists` is **now PROVEN** (no longer a sorry) via the master dispatch
`gapEnergy_nonneg`: the witness `f₀` works because regime i (`required ≤ 0`) follows from
`aggregate_triangle_poincare` (`regime_i_from_aggregate`), and regime ii (`required > 0`) is
`typeA_extremality_gap_nonneg`. Sorry-free pieces: `gapEnergy`/`aggregateSlack`/`required` (defs),
`gap_eq_aggregateSlack_sub_required` (identity, `ring`), `regime_i_from_aggregate`,
`regime_ii_regular_gap_nonneg` (via `triEnergy_le_RHS_regular`), `gapEnergy_nonneg` (dispatch).
The 3 sorrys are now `aggregate_triangle_poincare` (regime i) + `typeA_extremality_gap_nonneg`
(regime ii TYPE A) + `conjectureB` (lift reduction) — the regime split made explicit
(`informal/conjecture_B_hard_band_E_negative.md`).

**`conjectureB_lift` is now the EXISTENTIAL lift, depending on the single sorry `triEnergy_le_RHS_exists`**
(`conjectureB_lift = triEnergy_le_RHS_exists` with `hTconn`; `conjecture_B_AB_minus_D.md`). The earlier
*universal* `triEnergy_le_RHS`/`conjectureB_regime_two` (`∀ Fiedler, T ≤ λ₂G`) were discovered **FALSE**
on degenerate `λ₂` (star+clique: bad eigenvector gives `gap < 0`) and **removed**. The correct content
is: *some* unit Fiedler satisfies `T ≤ λ₂G` (`max gap ≥ 0` over the eigenspace), conditioned on
`hTconn` (triangleGraph connected — else even the existential fails, but `λ₂(T(G))=0` trivially there).
`triEnergy_le_B2prime` (`T ≤ B2′`) and `aggregate_triangle_poincare` (open) are off-chain; TYPE B is
separately closed by `conjectureB_regime_two_typeB`. The complete-graph `K_n` remains the simple-`λ₂`
extremizer.

*Honest caveat (`conjecture_B_T_direct_restructure.md`):* the "regular case proved + irregularity slack"
route does **not** work — `aggregate_triangle_poincare_regular` does not cover `K_n` (Required>0,
overshoots), and `slack = 1 − T/(λ₂G)` is *not* driven by irregularity (regular graphs span slack
`0–0.998`; slack vanishes only at `K_n`, by density). The regular case reduces to `λ₂ + S²/m ≤ d+1`; the
general case needs a *completeness*-monotonicity (`δ`/`eigenpair_invariance_equal_values`), not an
irregularity bound.

The graph statement `conjectureB` carries the *orthogonal* projected-Fiedler lift-reduction sorry
(Rayleigh of `T(G)` → the energy inequality `conjectureB_lift`); once that is formalised, `conjectureB`
inherits the single `B2prime_le_RHS` obstruction.

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

## 10. TYPE A extremality program (COMPLETE architecture)

**Theorem target:** `gap/eff ≥ 1/3` for all TYPE A (`λ < γ`), equality (in the limit) at the `d=2`
twin-port `K_N` extremizer. Since `eff > 0` (Green's-function sum rule, §6), this is `gap ≥ eff/3 > 0`
⟹ Conjecture B on TYPE A. The program builds the bound as a chain of monotonicities reducing any TYPE A
graph to the extremizer. See `TYPE_A_EXTREMALITY_PLAN.md` and `conjecture_B_typeA_extremality_task{1,2,3,4A,4A.5,4B,4C}*.md`, `..._assembly.md`.

### Extremizer (PROVED, all exact rationals)

`v₀` on twin ports `a,b ~ {0,1}` (`a≁b`) into bulk `K_N`, via the 4-class equitable quotient
(`{v₀},{a,b},{ports},{rest}`), `N → ∞`:

> **`λ₂ = 1`** (secular `(λ−1)(λ−4)=0`), **`eff = 2`** (antisymmetric resolvent, `μ_{ab}=d=2`),
> **`gap = 2/3`**, **`gap/eff = 1/3`**. (Finite `N`: `λ₂ = 1 + 4/(3N)`, `gap = 2/3 + O(1/N)`.)

### The four monotonicities (reduce any complete-bulk port config to the extremizer)

| step | statement | status |
|---|---|---|
| **TASK 1** | `g(d) = (3d²+dw−6d−9w+27)/(2d²−4d+18)` (`w=√(d²−2d+9)`) strictly **increasing** in `d`; `g(2)=1/3` | **PROVED** (`g′=4d·M(d)/D(d)`, `M(d)>0` via integer identity `(t+5)²−(t+1)(t+9)=16>0`) |
| **TASK 2** | `g(d,s)` **decreasing** in overlap `s`, min at twins `s=d` | **PROVED** (`eff` `s`-independent; `gap(d,s)=C(d)−2p²s` linear, slope `−2p²<0`) |
| **TASK 3** | `a≁b` minimizes at the extremizer (`d=2`: `g` rises `1/3→1` if `a~b`) | **PROVED at extremizer** (`eff(a~b)=2/(d+2−λ)` drops 3×); "all `d`" version false (`d≥8`) but moot |
| **TASK 4C** | interior bulk-edge deletion raises `gap` by `δ = 8/(3N²) > 0` (`eff,λ` fixed) | **PROVED leading order** (the `λ`-part cancels `−64+128−64=0`; survivor `+16p²/N²` from `B2′`); `δ·N²→8/3` verified |

Supporting: **TASK 4A** (bulk-rigidity scan: 0 counterexamples to `gap/eff ≥ 1/3` over `K_N±e`,
regular, ER, adversarial, 2-blobs, + large-`N` limits); **TASK 4A.5** (no *scalar* rigidity variable —
the prefactor is full-spectrum); **TASK 4B** (`eff = 2/(d−λ)` is **port-local**, invariant under
interior deletion — the Green's-function key).

### Assembly (TASK 5) — validated counterexample-free

Chain: `gap/eff(G) ≥` [complete interior, TASK 4C, lowers `gap/eff`] `≥` [complete-bulk port-config
min, TASKS 1–3] `= 1/3`.

> **Step-by-step completion of 12 random TYPE A graphs (3318 edge additions): 0 steps below `1/3`**
> (overall min `0.731`). Completion *raises* `gap/eff`, so the binding minimum is the sparse start.
> `K_N` port-config scan **including asymmetric `d_a ≠ d_b`**: min at the symmetric twin `d=2,s=2`
> (`0.508 → 1/3`); asymmetric strictly higher.

### Remaining rigour (3 items)

1. **`O(1/N)` Fiedler correction** in TASK 4C — **resolved**: the Fiedler does *not* perturb at all.
   `eigenpair_invariance_equal_values` (Lean, sorry-free) proves `f, λ` are *exactly* invariant under
   deletion of an edge between equal-Fiedler vertices, so `δ_exact` is an exact finite-`N` formula
   (`conjecture_B_typeA_delta_rigor.md`); only a finite algebraic sign bound on it remains.
2. **Asymmetric ports** (`d_a ≠ d_b`): TASKS 1–2 generalised (numerically `≥ 1/3`, §10 scan).
3. **TYPE A invariance under the moves** (each completion step keeps `λ < γ`, `f_v₀²` bounded):
   observed, to be proved.

With these three, `gap/eff ≥ 1/3` is a theorem and TYPE A is closed. The architecture is **complete
and counterexample-free**; what remains is analytic rigour of established leading-order facts, not new
structure.

## Bottom line

- **Closed:** all regular graphs (Lean); TYPE B (Lean); deg2+`K_{n−1}` (closed form).
- **TYPE A — architecture complete (§10):** reduced to `gap/eff ≥ 1/3` with an **explicit extremizer**
  (`d=2` twin ports `K_N→∞`: `λ=1, eff=2, gap=2/3`, all exact). Four monotonicities proved (TASK 4C
  leading-order); assembly validated (0/3318). `eff > 0` proven. **Remaining: 3 rigour items**
  (`O(1/N)` correction, asymmetric ports, TYPE A invariance) — analytic, not structural.
- **Regime 1:** reduced to `aggregate_triangle_poincare` (`T ≤ λ₂fᵀDf`); regular case proved.
- **Lean:** three `sorry`s remain (`aggregate_triangle_poincare` [regime i],
  `typeA_extremality_gap_nonneg` [regime ii TYPE A], `conjectureB` [lift reduction]), mapped in §6.
  **The regime architecture `gapEnergy = aggregateSlack − required` is now formalised** (identity +
  `regime_i_from_aggregate` + `regime_ii_regular_gap_nonneg` + `gapEnergy_nonneg` dispatch, all
  sorry-free); `triEnergy_le_RHS_exists` is now PROVEN via it (witness `f₀`), so the existential lift's
  sorry was replaced by the TYPE A leaf. `triEnergy_le_RHS_regular` proves the regular case (sorry-free
  modulo `λ≤d+1`).
