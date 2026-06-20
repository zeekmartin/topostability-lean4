# Conjecture B — consolidation status

Snapshot of the `λ₂(T(G)) ≤ λ₂(G)` campaign: formulations, proven Lean lemmas, the three-regime
classification, what is closed, what is open, which proof routes failed and why, and the current sharp
TYPE A obstruction. (Consolidation only — no new proof routes.)

---

## 1. Original conjecture

For a connected graph `G` with connected triangle graph `T(G)` (vertices = edges of `G`, two edges
adjacent in `T(G)` iff they lie in a common triangle):

> **`λ₂(T(G)) ≤ λ₂(G)`**  (algebraic connectivity of the triangle graph ≤ that of `G`).

Lean: `theorem conjectureB` (`ConjectureB.lean`).

## 2. Current equivalent formulations

Let `f` be a unit Fiedler vector of `G` (`L_G f = λ₂ f`), `g_e = f_a − f_b`, `h_e = f_a + f_b`,
`S = Σ_v d_v f_v`, `m = |E|`, `Q = D + A` (signless Laplacian), `T = Σ_e t_e g_e²` (triangle energy,
`t_e = |N(a)∩N(b)|`).

1. **Lift inequality** (`conjectureB_lift`): `B ⟸ T ≤ λ₂(fᵀQf − S²/m) = 2λ₂(2fᵀDf − λ₂ − S²/m)`.
2. **Triangle-free reduction**: `T ≤ B2′ ≤ λ₂G`, where
   `B2′ = Σ_e (min(d_a,d_b)−1) g_e²` and `λ₂G = λ₂(Σ_e h_e² − S²/m)`. The first `≤` is per-edge
   (`t_e ≤ min(d_a,d_b)−1`, `triCount_le_min_degree_sub_one`); the second is the open core.
3. **Gap decomposition**: `gap := λ₂G − B2′ = R″ + C`, with
   `R″ = λ₂(fᵀDf − λ₂ + 1 − S²/m)` and `C = Σ_{e, h=higher-deg}(d_h − d_l)f_h(f_h − f_l)`.
4. **Electrical form (TYPE A)**: `gap = Θ(eff_resist(a,b))`, `eff_resist = R_aa+R_bb−2R_ab` with
   `R = (L_H − λ)^{-1}` the core resolvent (see §8).

## 3. Proven Lean lemmas (sorry-free, in `ConjectureB.lean`)

| lemma | content |
|---|---|
| `triEnergy_diag_corr` | `T = 2Σ τ_v f_v² − 2Σ t_ij f_i f_j` (diagonal/correlation split) |
| `degAssort_covariance` | `𝒜 = dᵀ L (f∘f)` (degree–`f²` Laplacian covariance) |
| `B2prime_min_decomp` | `Σ(min(d_i,d_j)−1)g² = ½Σ(d_i+d_j)g² − ½Σ|d_i−d_j|g² − Σg²` |
| `triCount_le_min_degree_sub_one` | `t_e = |N(i)∩N(j)| ≤ min(d_i,d_j) − 1` (per-edge `T ≤ B2′`) |
| `lagrange_identity`, `sum_sq_mul_card_sub_sq` | Lagrange / variance identities |
| `lapMatrix_*`, `quadForm_*`, `neighbor_dirichlet_identity` | Laplacian quadratic-form toolkit |
| **`aggregate_triangle_poincare_regular`** | **`T ≤ 2λ·fᵀDf` for `d`-regular `G`** (Regime-1 base case, closed) |
| **`triEnergy_le_block_dirichlet`** | **`T ≤ W·D_block`** (TYPE B structural reduction) |
| **`typeB_triEnergy_bound`** | **`T ≤ (W·Cflat)·λ₂²`** given block flatness (TYPE B closure) |
| `conjectureB_lift` | regime split: `B ⟸` (aggregate Poincaré) ∧ (regime-two) |

Paper16 (block spectral lemmas, sorry-free): `poincare_on_block`, `block_gap`, `block_gap_lower`,
`quadform_edge_split`, `lapQuadForm_edge_split`, `block_fiedler_energy`.

## 4. Three-regime classification (empirical, 580-graph corpus + scaling)

Split on `Required = λ₂(λ₂ + S²/m − fᵀDf)`; `boundary_ratio` from the carrier/block geometry.
**Exhaustive and bimodal (0 graphs in the gap):**

| regime | criterion | count | mechanism |
|---|---|---|---|
| **Regime 1** | `Required ≤ 0` | 277 | `fᵀDf` large ⇒ `RHS ≥ λ₂fᵀDf`; reduces to aggregate Poincaré |
| **TYPE A** | `Required > 0`, `boundary_ratio < 1` | 226 | vertex bottleneck (deg-2 vertex on dense block) |
| **TYPE B** | `Required > 0`, `boundary_ratio > 2` | 77 | path/stub bottleneck on triangle-rich block |

`277 + 226 + 77 = 580`; `boundary_ratio` bimodal (nothing in `(1,2]`).

## 5. Closed regimes

- **TYPE B — fully closed (Lean, sorry-free).** `T = T_block` (path & boundary triangle-free ⇒
  `T_path = T_junction = 0`), `T_block ≤ W·D_block` (`triEnergy_le_block_dirichlet`), and with block
  flatness `D_block ≤ Cflat·λ₂²` (`poincare_on_block` on `G[B]`) ⇒ `T ≤ (W·Cflat)·λ₂² = O(λ₂²)`,
  while `RHS = Θ(λ₂)` ⇒ `T ≤ RHS` (`typeB_triEnergy_bound`).
- **Regime 1 — regular case closed.** `aggregate_triangle_poincare_regular` proves `T ≤ 2λ·fᵀDf` for
  `d`-regular `G`; in Regime 1 `RHS ≥ λ₂fᵀDf`, so `T ≤ RHS`. (Irregular case open — see §7.)
- **TYPE A complete core — closed in closed form.** `gap = 10(n−3)/m > 0` exactly (sympy-proven,
  `gap(ρ=n−2, λ=2) = 20(n−3)/(n²−3n+6) = 10(n−3)/m`); manifestly positive. (General TYPE A open.)

## 6. Open Lean lemmas (the three `sorry`s)

| `sorry` (line) | statement | mathematical obstruction |
|---|---|---|
| **`aggregate_triangle_poincare`** (598) | `T ≤ 2λ·fᵀDf` (general `G`) | **Regime 1 (irregular).** Holds 277/277 empirically; regular case proved (`…_regular`). The irregular case is the deg2+dense bottleneck where `L_min` does not commute with `L` (no eigenbasis collapse). |
| **`conjectureB_regime_two`** (675) | `T ≤ 2λ(2fᵀDf − λ − S²/m)` when `Required > 0` | **TYPE A ∪ TYPE B.** TYPE B is closed structurally (`typeB_triEnergy_bound`, modulo wiring the block decomposition). **TYPE A is the live obstruction** (§8). |
| **`conjectureB`** (702) | `λ₂(T(G)) ≤ λ₂(G)` (graph statement) | **Lift reduction.** Needs `conjectureB_lift` (done modulo the two above) + the projected-Fiedler lift `h′ = Bᵀf − (S/m)1_E ⊥ 1_E` with `t_ab ≤ min−1` (`triCount_le_min_degree_sub_one`); the lift reduction itself is not yet formalised. |

## 7. Failed proof routes (and why)

| route | why it fails |
|---|---|
| **Γ₂ / Bochner curvature** | lossy; the local curvature bound overshoots, gap too small |
| **Second variation of natural test vectors** | overshoots; the gap is sub-leading to the variation |
| **Scalar / structured S-procedure** | multiplier `α` blows up (`~n^{1.18}–n²` on deg2+dense); the `−L_min` block indefiniteness is the obstruction. The regular collapse `M_α = gap·I` needs `[L_min,L]=0`, false for irregular (`‖[L_min,L]‖ ≠ 0`). |
| **Driver vs correction** (`λρ‖f_H‖²` + correction) | `correction` is `O(1)`, **not** `O(η²)` (`\|corr\|/η² → 37000`); dominated by the η-independent `−λS²/m` and degree terms. `driver ≈ \|correction\|` (both `O(1)`, nearly cancel); `driver > \|corr\|` is circular (= gap>0) with vanishing margin. |
| **Polynomial / resultant elimination** | no **polynomial exact secular** (the mean-field cubic is only approximate, qualitatively wrong for the complete core). `Res(P,Num) ≡ 0` (trivial null mode `λ=0`); the reduced resultant vanishes from the spurious high mode `λ_big ≈ ρ`, not the bottleneck `λ*`. `Num` sign-indefinite near `λ*` for dense `ρ` (Sturm = 2). `λ*` irrational, inseparable from spurious modes. |
| **Monotonicity / complete-core extremality** | the complete core is **not** the gap-minimizer: deleting an **attachment-incident** edge (lowering `d_a, d_b`) decreases gap below complete (nH=30: `0.629 < 0.641`). Monotone only in bulk-bulk edges. |
| **Resolvent 2×2 Schur PSD** | `gap > 0` is **not** a 2×2 PSD condition: `gap = POS − NEG`, both `O(n)`, nearly cancelling; `R₂ ≻ 0 ⟺ λ < γ` certifies TYPE A membership, not `gap > 0`. |
| **`gap/eff_resist` closed form** | not a closed function of the 2×2 block: needs higher resolvent moments (`M2` and beyond; regression residual stays `~13%` of range). |

**Common root cause:** in TYPE A, `gap` is the `O(1/n)` residual of two matched `O(1)` (or `O(n)`)
quantities at an **irrational secular root** that cannot be algebraically isolated; the obstruction is
concentrated at the `v₀–a–b` attachment junction.

## 8. Current sharp TYPE A obstruction

For `G = H + v₀` (`v₀` degree-2, attached at `a, b`), `γ = λ₂(H)`, TYPE A condition `λ₂(G) < γ`:

- **Scale (proven):** `gap = Θ(eff_resist(a,b))`, where
  `eff_resist = R_aa + R_bb − 2R_ab = Σ_{k≥2}(φ_k(a)−φ_k(b))²/(μ_k − λ)` (Green's-function sum rule,
  weights sum to 2), so `2/(μ_max−λ) ≤ eff_resist ≤ 2/(γ−λ)`. **`eff_resist > 0` is manifest**
  (`⟺ R₂ ≻ 0 ⟺ λ < γ`, Courant–Fischer). `γ·eff_resist ∈ [0.5, 2.2]`.
- **Secular (clean):** symmetric attachments give `λ = 2n/((n−1)(1+R_+))`, `R_+ = (R_aa+R_bb)/2 + R_ab`.
- **Open prefactor:** writing `gap = eff_resist · (gap/eff_resist)`,

  > **`gap > 0 ⟺ gap/eff_resist ≥ c₀ > 0`**, empirically `gap/eff_resist ∈ [2.3, 10]`
  > (`inf ≈ 2.3`; complete core at the maximum `10`).

  The prefactor `gap/eff_resist` is **bounded away from 0** but is **not** a finite resolvent invariant
  (no SOS / 2×2-block / closed form; depends on the full core spectrum). This single positive lower
  bound is the entire remaining content of TYPE A.

**Verification status:** `gap > 0` holds on every tested TYPE A graph (corpus + scaling + adversarial
stress-tests, min gap `> 0` throughout); the equality case is empty (`T = λ₂G` impossible). The
conjecture is believed true; what is missing is a proof of the prefactor lower bound `gap/eff ≥ c₀`.

---

## Bottom line

- **Regime 1:** open lemma `aggregate_triangle_poincare` (`T ≤ λ₂fᵀDf`); regular case proved.
- **TYPE B:** **closed** (Lean, sorry-free) given the standard `poincare_on_block` block-flatness input.
- **TYPE A:** complete core **closed in closed form**; general case reduced to the single sharp
  inequality `gap/eff_resist ≥ c₀ > 0`, with `eff_resist > 0` already proven. No algebraic, extremal,
  resolvent, or electrical invariant pins down the prefactor — that is where a new idea is required.
- **Three `sorry`s** remain in `ConjectureB.lean`, mapped above to (Regime 1) / (TYPE A) / (lift
  reduction).

See the per-round `informal/conjecture_B_*.md` for full derivations and data.
