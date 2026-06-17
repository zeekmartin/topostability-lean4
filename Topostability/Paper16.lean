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

end Topostability
