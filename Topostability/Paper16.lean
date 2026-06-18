import Topostability.Shared
import Mathlib.Analysis.MeanInequalities

/-!
# Paper 16 — block spectral lemmas for Conjecture B

Two spectral lemmas underpinning the `Required > 0` block argument (see the `informal/`
analyses `conjecture_B_block_proof`, `_final_threshold`, `_final_classification`).

* **`poincare_on_block`** — the resolvent / Poincaré-on-block bound. For a connected graph,
  a zero-sum vector `f`, and `λ < λ₂`, if `g = (L − λI)f` then `‖f‖²(λ₂ − λ)² ≤ ‖g‖²`.
  This is the rigorous form of "the spectral gap forces `f` near-uniform": the non-constant
  part of `f` is controlled by the forcing `g` over the gap. Proof = Rayleigh bound
  (`algebraicConnectivity_le_rayleigh`) + Cauchy–Schwarz, **no eigendecomposition needed**.

* **`block_gap`** — the Courant–Fischer block-gap inequality. For a zero-sum competitor `g`
  with `gᵀL_G g = blockEnergy + boundaryEnergy`, minimality gives
  `λ₂(G)·‖g‖² ≤ blockEnergy + boundaryEnergy`, i.e. `blockEnergy ≥ λ₂(G)‖g‖² − boundaryEnergy`.
  Applied with `g` = Fiedler of `G[B]` extended by `0` on the carriers and
  `blockEnergy = λ₂(G[B])·‖g‖²`, this is `λ₂(G[B]) ≥ λ₂(G) − boundary/‖g‖²`. The
  edge-split identity `gᵀL_G g = blockEnergy + boundaryEnergy` and the identification
  `blockEnergy = λ₂(G[B])‖g‖²` (block Fiedler eigen-equation on the induced subgraph) are the
  inputs supplied as hypotheses; the Courant–Fischer step is proved here via
  `algebraicConnectivity_le_rayleigh`.
-/

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Lemma 1 — Poincaré-on-block (resolvent bound).**
For connected `G` (≥ 2 vertices), a nonzero zero-sum vector `f`, and `lam < λ₂(G)`, the
resolvent vector `g := (L_G − lam·I)f` controls the size of `f`:
`(∑ f²)·(λ₂(G) − lam)² ≤ ∑ g²`.

Equivalently `‖f‖² ≤ ‖g‖²/(λ₂ − lam)²`: the spectral gap above `lam` damps `f` relative to
its forcing. Proof: `fᵀg = fᵀL_G f − lam‖f‖² ≥ (λ₂ − lam)‖f‖²` (Rayleigh bound), and
`fᵀg ≤ ‖f‖‖g‖` (Cauchy–Schwarz), so `(λ₂ − lam)‖f‖ ≤ ‖g‖`. -/
lemma poincare_on_block (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (f : V → ℝ) (hf : f ≠ 0) (hsum : ∑ v : V, f v = 0)
    (lam : ℝ) (hlam : lam < algebraicConnectivity G hV) :
    (∑ v : V, (f v) ^ 2) * (algebraicConnectivity G hV - lam) ^ 2
      ≤ ∑ v : V, ((G.lapMatrix ℝ).mulVec f v - lam * f v) ^ 2 := by
  -- ‖f‖² > 0
  have hSfpos : 0 < ∑ v : V, (f v) ^ 2 := by
    apply Finset.sum_pos' (fun i _ => sq_nonneg (f i))
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra h; push_neg at h; exact hf (funext h)
    exact ⟨v, Finset.mem_univ _, by positivity⟩
  have hAlam : 0 < algebraicConnectivity G hV - lam := by linarith
  -- quadratic form as an explicit sum
  have htlm : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f
      = ∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f) v := by
    rw [Matrix.toLinearMap₂'_apply']; rfl
  -- Rayleigh bound: λ₂·‖f‖² ≤ fᵀL f
  have hray : algebraicConnectivity G hV * (∑ v : V, (f v) ^ 2)
      ≤ ∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f) v := by
    have h := algebraicConnectivity_le_rayleigh G hconn hV f hf hsum
    rw [le_div_iff₀ hSfpos, htlm] at h
    exact h
  -- P := fᵀg = fᵀL f − lam‖f‖²
  have hPeq : (∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f v - lam * f v))
      = (∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f) v) - lam * (∑ v : V, (f v) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  -- P ≥ (λ₂ − lam)‖f‖²
  have hPge : (algebraicConnectivity G hV - lam) * (∑ v : V, (f v) ^ 2)
      ≤ ∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f v - lam * f v) := by
    rw [hPeq]; nlinarith [hray]
  -- Cauchy–Schwarz: P² ≤ ‖f‖²·‖g‖²
  have hcs : (∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f v - lam * f v)) ^ 2
      ≤ (∑ v : V, (f v) ^ 2)
          * (∑ v : V, ((G.lapMatrix ℝ).mulVec f v - lam * f v) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f
      (fun v => (G.lapMatrix ℝ).mulVec f v - lam * f v)
  -- square the lower bound: ((λ₂−lam)‖f‖²)² ≤ P²
  have hL0nn : 0 ≤ (algebraicConnectivity G hV - lam) * (∑ v : V, (f v) ^ 2) :=
    le_of_lt (mul_pos hAlam hSfpos)
  have hsq : ((algebraicConnectivity G hV - lam) * (∑ v : V, (f v) ^ 2))
        * ((algebraicConnectivity G hV - lam) * (∑ v : V, (f v) ^ 2))
      ≤ (∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f v - lam * f v))
        * (∑ v : V, f v * ((G.lapMatrix ℝ).mulVec f v - lam * f v)) :=
    mul_self_le_mul_self hL0nn hPge
  -- chain and cancel ‖f‖²
  have hchain : (∑ v : V, (f v) ^ 2)
        * ((∑ v : V, (f v) ^ 2) * (algebraicConnectivity G hV - lam) ^ 2)
      ≤ (∑ v : V, (f v) ^ 2)
        * (∑ v : V, ((G.lapMatrix ℝ).mulVec f v - lam * f v) ^ 2) := by
    nlinarith [hsq, hcs]
  exact le_of_mul_le_mul_left hchain hSfpos

/-- **Lemma 2 — Courant–Fischer block gap.**
For connected `G` (≥ 2 vertices), a nonzero zero-sum competitor `g`, and a decomposition of
its Laplacian quadratic form `gᵀL_G g = blockEnergy + boundaryEnergy`, minimality of `λ₂`
gives `λ₂(G)·‖g‖² ≤ blockEnergy + boundaryEnergy`.

Used with `g` = Fiedler of `G[B]` extended by `0` on `V∖B`, `blockEnergy = λ₂(G[B])·‖g‖²`
(block Fiedler eigen-equation) and `boundaryEnergy = Σ_{v∈B, u∉B, u∼v} g_v²` (the B–C cut),
the decomposition `gᵀL_G g = λ₂(G[B])‖g‖² + boundaryEnergy` (standard Laplacian edge split)
turns this into `λ₂(G[B]) ≥ λ₂(G) − boundaryEnergy/‖g‖²`. The Courant–Fischer step is the
content proved here (`algebraicConnectivity_le_rayleigh`); the edge split and the block
eigen-equation are the supplied inputs. -/
lemma block_gap (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (g : V → ℝ) (hg : g ≠ 0) (hsum : ∑ v : V, g v = 0)
    (blockEnergy boundaryEnergy : ℝ)
    (hdecomp : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) g g = blockEnergy + boundaryEnergy) :
    algebraicConnectivity G hV * (∑ v : V, (g v) ^ 2) ≤ blockEnergy + boundaryEnergy := by
  have hpos : 0 < ∑ v : V, (g v) ^ 2 := by
    apply Finset.sum_pos' (fun i _ => sq_nonneg (g i))
    obtain ⟨v, hv⟩ : ∃ v, g v ≠ 0 := by
      by_contra h; push_neg at h; exact hg (funext h)
    exact ⟨v, Finset.mem_univ _, by positivity⟩
  have h := algebraicConnectivity_le_rayleigh G hconn hV g hg hsum
  rw [le_div_iff₀ hpos, hdecomp] at h
  exact h

/-- The gap form of `block_gap`: `blockEnergy ≥ λ₂(G)·‖g‖² − boundaryEnergy`. With
`blockEnergy = λ₂(G[B])·‖g‖²` this is the block-gap inequality
`λ₂(G[B]) ≥ λ₂(G) − boundaryEnergy/‖g‖²`. -/
lemma block_gap_lower (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (g : V → ℝ) (hg : g ≠ 0) (hsum : ∑ v : V, g v = 0)
    (blockEnergy boundaryEnergy : ℝ)
    (hdecomp : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) g g = blockEnergy + boundaryEnergy) :
    algebraicConnectivity G hV * (∑ v : V, (g v) ^ 2) - boundaryEnergy ≤ blockEnergy := by
  have := block_gap G hconn hV g hg hsum blockEnergy boundaryEnergy hdecomp
  linarith

/-- **Edge split of the Laplacian quadratic form (ordered double-sum form).**
For `g` supported on `B` (`g v = 0` for `v ∉ B`), the ordered Dirichlet double sum splits into
the within-`B` part and a boundary part. Key point: on every edge not fully inside `B`, at
least one endpoint has `g = 0`, so there `g i · g j = 0` and `(g i − g j)² = g i² + g j²`. -/
lemma quadform_edge_split (g : V → ℝ) (B : Finset V) (hsupp : ∀ v, v ∉ B → g v = 0) :
    (∑ i : V, ∑ j : V, if G.Adj i j then (g i - g j) ^ 2 else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then (g i - g j) ^ 2 else 0)
        + (∑ i : V, ∑ j : V,
            if G.Adj i j ∧ ¬ (i ∈ B ∧ j ∈ B) then g i ^ 2 + g j ^ 2 else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hadj : G.Adj i j
  · by_cases hB : i ∈ B ∧ j ∈ B
    · rw [if_pos hadj, if_pos ⟨hadj, hB.1, hB.2⟩, if_neg (fun h => h.2 hB), add_zero]
    · have hz : g i * g j = 0 := by
        rcases not_and_or.mp hB with hi | hj
        · rw [hsupp i hi]; ring
        · rw [hsupp j hj]; ring
      rw [if_pos hadj, if_neg (fun h => hB ⟨h.2.1, h.2.2⟩), if_pos ⟨hadj, hB⟩, zero_add]
      nlinarith [hz]
  · rw [if_neg hadj, if_neg (fun h => hadj h.1), if_neg (fun h => hadj h.1), add_zero]

/-- **Bridge: the Laplacian quadratic form decomposes into block + boundary energies.**
For `g` supported on `B`, `gᵀL_G g = blockEnergy + boundaryEnergy` with
`blockEnergy = ½·Σ_{i,j∈B, i~j}(g_i−g_j)²` (the within-`B` Dirichlet form, equal to the
Laplacian quadratic form of the induced subgraph `G[B]`) and
`boundaryEnergy = ½·Σ_{i,j, i~j, ¬both∈B}(g_i²+g_j²)` (the `B`–`Bᶜ` cut). This supplies the
`hdecomp` hypothesis of `block_gap`/`block_gap_lower` directly from the graph Laplacian. -/
lemma lapQuadForm_edge_split (g : V → ℝ) (B : Finset V) (hsupp : ∀ v, v ∉ B → g v = 0) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) g g
      = (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then (g i - g j) ^ 2 else 0) / 2
        + (∑ i : V, ∑ j : V,
            if G.Adj i j ∧ ¬ (i ∈ B ∧ j ∈ B) then g i ^ 2 + g j ^ 2 else 0) / 2 := by
  rw [SimpleGraph.lapMatrix_toLinearMap₂', quadform_edge_split G g B hsupp]
  ring

/-- **Block Fiedler eigenvalue identification.**
If `g` (extended by `0` off `B`) is, on `B`, an eigenvector of the induced Laplacian
`L_{G[B]}` with eigenvalue `lamB` — stated in row form
`∀ i, Σ_{j: i~j, i,j∈B}(g i − g j) = lamB·g i` (this is `(L_{G[B]} g)_i = lamB·g_i`) — then the
within-`B` Dirichlet (block) energy equals `2·lamB·‖g‖²`:
`Σ_{i,j∈B, i~j}(g_i−g_j)² = 2·lamB·Σ_v g_v²`. So in `lapQuadForm_edge_split` the block energy
`blockEnergy/2 = lamB·‖g‖²` is exactly `λ₂(G[B])·‖g‖²` when `lamB = λ₂(G[B])` and `g` its
Fiedler. Pure summation-by-parts: expand the square, use the symmetry of the within-`B`
predicate, and substitute the row eigen-equation. -/
lemma block_fiedler_energy (g : V → ℝ) (B : Finset V) (lamB : ℝ)
    (hrow : ∀ i, (∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i - g j else 0) = lamB * g i) :
    (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then (g i - g j) ^ 2 else 0)
      = 2 * lamB * (∑ v : V, g v ^ 2) := by
  -- expand the square into S1 − 2·S2 + S3
  have hexp : (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then (g i - g j) ^ 2 else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i ^ 2 else 0)
        - 2 * (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i * g j else 0)
        + (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g j ^ 2 else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  -- symmetry of the within-B predicate: S3 = S1
  have hsymm : (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g j ^ 2 else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : G.Adj i j ∧ i ∈ B ∧ j ∈ B
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.2, h.2.1⟩]
    · rw [if_neg h, if_neg (fun hh => h ⟨hh.1.symm, hh.2.2, hh.2.1⟩)]
  -- S2 = S1 − lamB·‖g‖²  (row eigen-equation, factored per i)
  have hS2 : (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i * g j else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i ^ 2 else 0)
        - lamB * (∑ v : V, g v ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hC : (∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i else 0)
          - (∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g j else 0) = lamB * g i := by
      rw [← Finset.sum_sub_distrib, ← hrow i]
      exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    have hLHS : (∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i * g j else 0)
        = g i * (∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g j else 0) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    have hSi : (∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i ^ 2 else 0)
        = g i * (∑ j : V, if G.Adj i j ∧ i ∈ B ∧ j ∈ B then g i else 0) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    rw [hLHS, hSi]
    linear_combination (-(g i)) * hC
  rw [hexp, hsymm, hS2]; ring

end Topostability
