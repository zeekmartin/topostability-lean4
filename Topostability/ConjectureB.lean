import Topostability.Defs
import Topostability.Shared
import Topostability.Paper14
import Topostability.Paper15
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Conjecture B — proof skeleton

Conjecture B: for a connected graph `G` with the triangle graph `T(G)` connected,
`λ₂(T(G)) ≤ λ₂(G)`.

Via the projected Fiedler lift this reduces to the **triangle-energy lift inequality**
`T ≤ λ₂·(fᵀQf − S²/m)` (`Q = D+A`, `S = Σ d_v f_v`, `m = |E|`, `f` the unit Fiedler).
We prove that inequality by a **regime split** on the sign of
`Required := λ₂(λ₂ + S²/m − fᵀDf)`:

* **Regime (i) `Required ≤ 0`** — closed here, modulo the aggregate triangle-Poincaré
  `T ≤ λ₂·fᵀDf` (`aggregate_triangle_poincare`, open). Algebra: `Required ≤ 0` gives
  `fᵀDf ≥ λ₂ + S²/m`, hence `fᵀQf − S²/m = 2fᵀDf − λ₂ − S²/m ≥ fᵀDf`, so
  `T ≤ λ₂fᵀDf ≤ λ₂(fᵀQf − S²/m)`.
* **Regime (ii) `Required > 0`** — the bottleneck regime (`conjectureB_regime_two`, open;
  empirically `Deficit/Required ≥ 1.7`).

Everything is stated in the **ordered** form `T_ord = Σ_{i,j}[i~j]|N(i)∩N(j)|(f_i−f_j)²`
(`= 2·Σ_{ab∈E} t_ab(f_a−f_b)²`, matching `apex_triangle_energy_identity` in `Paper15`),
so the inequalities carry a factor `2`. Supporting facts in the repo: the apex identity
(`Paper15`), value/gradient hub-flatness (`Paper14`), and `triCount_le_min_degree_sub_one`.
-/

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ordered triangle (Dirichlet) energy
`T_ord = Σ_{i,j} [i~j] · |N(i)∩N(j)| · (f_i − f_j)²`. Equals `2·Σ_{ab∈E} t_ab(f_a−f_b)²`. -/
def triEnergy (f : V → ℝ) : ℝ :=
  ∑ i : V, ∑ j : V,
    if G.Adj i j then ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) * (f i - f j) ^ 2
    else 0

/-- `fᵀDf = Σ_v d_v · f_v²`. -/
def degQuad (f : V → ℝ) : ℝ := ∑ v : V, (G.degree v : ℝ) * (f v) ^ 2

/-- `S = Σ_v d_v · f_v`. -/
def degLin (f : V → ℝ) : ℝ := ∑ v : V, (G.degree v : ℝ) * f v

/-- Triangle degree `τ_v = Σ_{u∼v} |N(v)∩N(u)|` (= twice the number of triangles through `v`).
Appears as the diagonal weight in `triEnergy_diag_corr`. -/
def triDeg (v : V) : ℝ := ∑ u : V, if G.Adj v u then (triCount G v u : ℝ) else 0

/-- **Diagonal/correlation identity (algebraic — no spectral hypothesis).**

`triEnergy = 2·Σ_v τ_v f_v² − 2·Σ_{i,j}[i∼j] t_ij f_i f_j`, obtained by expanding the square
`(f_i−f_j)² = f_i²+f_j²−2f_i f_j` and collapsing the two diagonal terms by symmetry of
`t_ij = |N(i)∩N(j)|`. This is the exact decomposition underlying the nodal analysis in
`informal/conjecture_B_nodal_decomposition.md`: the second sum is the triangle correlation
`C`, which splits globally into a same-sign reservoir minus the hard cross mass. -/
lemma triEnergy_diag_corr (f : V → ℝ) :
    triEnergy G f
      = 2 * (∑ i : V, triDeg G i * (f i) ^ 2)
        - 2 * (∑ i : V, ∑ j : V,
            if G.Adj i j then (triCount G i j : ℝ) * (f i * f j) else 0) := by
  simp only [triEnergy, triDeg, triCount]
  set C : V → V → ℝ := fun i j => ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) with hC
  have hCsymm : ∀ a b : V, C a b = C b a := by
    intro a b; simp only [hC]; rw [Finset.inter_comm]
  have hpull : ∀ i : V, (∑ j : V, if G.Adj i j then C i j * (f i) ^ 2 else 0)
      = (∑ j : V, if G.Adj i j then C i j else 0) * (f i) ^ 2 := by
    intro i; rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : G.Adj i j <;> simp [h]
  have hsymm : (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f j) ^ 2 else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i) ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : G.Adj a b
    · have hba : G.Adj b a := h.symm
      rw [if_pos h, if_pos hba, hCsymm b a]
    · have hba : ¬ G.Adj b a := fun x => h x.symm
      rw [if_neg h, if_neg hba]
  have hexp : ∀ i j : V,
      (if G.Adj i j then C i j * (f i - f j) ^ 2 else 0)
      = (if G.Adj i j then C i j * (f i) ^ 2 else 0)
        + (if G.Adj i j then C i j * (f j) ^ 2 else 0)
        - 2 * (if G.Adj i j then C i j * (f i * f j) else 0) := by
    intro i j; by_cases h : G.Adj i j <;> simp [h] <;> ring
  calc (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i - f j) ^ 2 else 0)
      = (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i) ^ 2 else 0)
          + (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f j) ^ 2 else 0)
          - 2 * (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i * f j) else 0) := by
        simp_rw [hexp]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (∑ i : V, (∑ j : V, if G.Adj i j then C i j else 0) * (f i) ^ 2)
          - 2 * (∑ i : V, ∑ j : V, if G.Adj i j then C i j * (f i * f j) else 0) := by
        rw [hsymm, ← Finset.sum_add_distrib]
        simp_rw [hpull, ← two_mul]
        rw [← Finset.mul_sum]

/-- **Diagonal/correlation identity, surplus form.** For any scalar `lam`,
`triEnergy − 2·lam·degQuad = 2·Σ_v (τ_v − lam·d_v) f_v² − 2·Σ_{i,j}[i∼j] t_ij f_i f_j`.
The aggregate triangle-Poincaré `triEnergy ≤ 2·λ₂·degQuad` is therefore equivalent to
`Σ_v(τ_v−λ₂d_v)f_v² ≤ Σ_{i,j}[i∼j] t_ij f_i f_j` (diagonal ≤ triangle correlation). -/
lemma triEnergy_sub_two_lam_degQuad (f : V → ℝ) (lam : ℝ) :
    triEnergy G f - 2 * lam * degQuad G f
      = 2 * (∑ i : V, (triDeg G i - lam * (G.degree i : ℝ)) * (f i) ^ 2)
        - 2 * (∑ i : V, ∑ j : V,
            if G.Adj i j then (triCount G i j : ℝ) * (f i * f j) else 0) := by
  rw [triEnergy_diag_corr, degQuad]
  have step : (∑ i : V, (triDeg G i - lam * (G.degree i : ℝ)) * (f i) ^ 2)
      = (∑ i : V, triDeg G i * (f i) ^ 2) - lam * (∑ v : V, (G.degree v : ℝ) * (f v) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [step]; ring

/-- **Row equation (algebraic).** For any Laplacian eigenpair `(lam, f)` (`L f = lam • f`),
the adjacency satisfies `A f = D f − lam • f` (`A = adjMatrix`, `D = degMatrix`, `L = D − A`). -/
lemma adjMatrix_mulVec_fiedler (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    (G.adjMatrix ℝ).mulVec f = (G.degMatrix ℝ).mulVec f - lam • f := by
  have hLDA : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
  rw [hLDA, Matrix.sub_mulVec] at heig
  rw [← heig]; abel

/-- **Triangle-level row equation (algebraic).** `A² f = A·(D f) − lam·(D f − lam·f)`. Since
`(A²)_{vu} = |N(v)∩N(u)|`, this lifts the row equation to the triangle level — the exact identity
behind the domain-local triangle analysis (`informal/conjecture_B_domain_triangle_perron.md`).
The triangle *energy* uses the Hadamard weight `A∘A²`, not `A²`, so this recursion bridges to
triangles only up to the open 2-path (non-adjacent common-neighbour) terms — see
`informal/conjecture_B_A2_triangle_gap.md`. -/
lemma adjSq_mulVec_fiedler (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    ((G.adjMatrix ℝ) ^ 2).mulVec f
      = (G.adjMatrix ℝ).mulVec ((G.degMatrix ℝ).mulVec f)
        - lam • ((G.degMatrix ℝ).mulVec f - lam • f) := by
  have hA := adjMatrix_mulVec_fiedler G f lam heig
  rw [pow_two, ← Matrix.mulVec_mulVec, hA,
      Matrix.mulVec_sub, Matrix.mulVec_smul, hA]

/-- **Apex sum-of-squares identity (algebraic, symmetry only).** `fᵀA²f = Σ_v ((A f)_v)²`, i.e.
the full 2-path quadratic form is the sum over apices `c` of the squared neighbourhood sums
`(A f)_c = Σ_{a∈N(c)} f_a`. With the eigen-equation `A f = (D−lam)f` this equals
`Σ_v (d_v−lam)² f_v²`, the recursion that controls both the closed (triangle) and open 2-path
energies. No spectral hypothesis is needed for this form. -/
lemma quadForm_adjSq_eq_normSq (f : V → ℝ) :
    dotProduct f (((G.adjMatrix ℝ) ^ 2).mulVec f)
      = ∑ v : V, ((G.adjMatrix ℝ).mulVec f v) ^ 2 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      show (G.adjMatrix ℝ).transpose = G.adjMatrix ℝ from G.transpose_adjMatrix]
  simp only [dotProduct, pow_two]

/-- **Quadratic form of the eigen-equation (algebraic).** `fᵀAf = fᵀDf − lam·(f·f)` for any
Laplacian eigenpair `(lam, f)` (`L f = lam • f`, `A = adjMatrix`, `D = degMatrix`). For a unit
vector this is `fᵀAf = fᵀDf − lam`, the bridge `lam·fᵀAf = lam(fᵀDf − lam)` used to recast the
open-2-path reformulation as `Open + 𝒜 ≥ lam·fᵀAf` (`informal/conjecture_B_hub_correction.md`). -/
lemma quadForm_adjMatrix_fiedler (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    dotProduct f ((G.adjMatrix ℝ).mulVec f)
      = dotProduct f ((G.degMatrix ℝ).mulVec f) - lam * dotProduct f f := by
  rw [adjMatrix_mulVec_fiedler G f lam heig]
  simp only [dotProduct]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Degree-assortativity edge identity (algebraic, symmetry only).** The diagonal
`Σ_v(σ_v − d_v²)f_v²` (`σ_v = Σ_{c∼v}d_c`), written as `Σ_{i,j}[i∼j](d_j−d_i)f_i²`, equals the
edge-antisymmetry `−½·Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)`. This is the negative (high-degree hub)
part of the diagonal `R_v` in the open-2-path reformulation of `aggregate_triangle_poincare`
(`informal/conjecture_B_open2path_gap.md`): the hub negativity is an edge antisymmetry between
degree and `f²`. No spectral hypothesis. -/
lemma degAssort_edge_identity (f : V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then ((G.degree j : ℝ) - G.degree i) * (f i) ^ 2 else 0)
      = - (1 / 2) * ∑ i : V, ∑ j : V,
          (if G.Adj i j then ((G.degree i : ℝ) - G.degree j) * ((f i) ^ 2 - (f j) ^ 2) else 0) := by
  set A1 : V → V → ℝ :=
    fun i j => if G.Adj i j then ((G.degree j : ℝ) - G.degree i) * (f i) ^ 2 else 0 with hA1
  set A2 : V → V → ℝ :=
    fun i j => if G.Adj i j then ((G.degree i : ℝ) - G.degree j) * ((f i) ^ 2 - (f j) ^ 2) else 0
    with hA2
  have hpt : ∀ i j : V, A1 i j + A1 j i = - A2 i j := by
    intro i j; simp only [hA1, hA2]
    by_cases h : G.Adj i j
    · have h' : G.Adj j i := h.symm
      rw [if_pos h, if_pos h', if_pos h]; ring
    · have h' : ¬ G.Adj j i := fun x => h x.symm
      rw [if_neg h, if_neg h', if_neg h]; ring
  have hswap : (∑ i : V, ∑ j : V, A1 i j) = ∑ i : V, ∑ j : V, A1 j i := Finset.sum_comm
  have hsum : (∑ i : V, ∑ j : V, A1 i j) + (∑ i : V, ∑ j : V, A1 j i)
      = ∑ i : V, ∑ j : V, - A2 i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  rw [← hswap] at hsum
  have hneg : (∑ i : V, ∑ j : V, - A2 i j) = - ∑ i : V, ∑ j : V, A2 i j := by
    simp only [Finset.sum_neg_distrib]
  rw [hneg] at hsum
  linarith [hsum]

/-- **Laplacian bilinear (Dirichlet) form (algebraic, no spectral hypothesis).** For any vectors
`u, w`, `uᵀ L w = Σ_{i,j}[i∼j] u_i (w_i − w_j)`. The bilinear extension of the Dirichlet energy;
specialised below at `u = d`, `w = f∘f` to identify the assortativity correction as a covariance. -/
lemma lapMatrix_bilin (u w : V → ℝ) :
    dotProduct u ((G.lapMatrix ℝ).mulVec w)
      = ∑ i : V, ∑ j : V, if G.Adj i j then u i * (w i - w j) else 0 := by
  have hrow : ∀ i : V, ((G.lapMatrix ℝ).mulVec w) i
      = ∑ j : V, if G.Adj i j then (w i - w j) else 0 := by
    intro i
    have hLDA : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
    rw [hLDA, Matrix.sub_mulVec, Pi.sub_apply]
    rw [show (G.degMatrix ℝ).mulVec w i = (G.degree i : ℝ) * w i from by
      simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]]
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [show (∑ j : V, if G.Adj i j then (w i - w j) else 0)
        = ∑ j ∈ G.neighborFinset i, (w i - w j) from by
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]]
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : G.Adj i j <;> simp [h]

/-- **Covariance form of the degree–Fiedler assortativity (algebraic, no spectral hypothesis).**
`𝒜 = dᵀ L (f∘f) = ½ Σ_{i,j}[i∼j](d_i−d_j)(f_i²−f_j²)`: the load-bearing hub-correction term in the
open-2-path reformulation of `aggregate_triangle_poincare` is exactly the graph-Laplacian
*covariance* of the degree vector `d` and the squared Fiedler vector `f∘f`
(`informal/conjecture_B_global_summation_parts.md`). It is `≤ 0` whenever degree and `f²` are
anti-monotone across edges (hub-flatness). Specialises `lapMatrix_bilin` at `u = d`, `w = f∘f`. -/
lemma degAssort_covariance (f : V → ℝ) :
    dotProduct (fun v => (G.degree v : ℝ)) ((G.lapMatrix ℝ).mulVec (fun v => (f v) ^ 2))
      = (1 / 2) * ∑ i : V, ∑ j : V,
          (if G.Adj i j then ((G.degree i : ℝ) - G.degree j) * ((f i) ^ 2 - (f j) ^ 2) else 0) := by
  rw [lapMatrix_bilin G]
  set a : V → V → ℝ :=
    fun i j => if G.Adj i j then (G.degree i : ℝ) * ((f i) ^ 2 - (f j) ^ 2) else 0 with ha
  set B : V → V → ℝ :=
    fun i j => if G.Adj i j then ((G.degree i : ℝ) - G.degree j) * ((f i) ^ 2 - (f j) ^ 2) else 0
    with hB
  have hpt : ∀ i j : V, B i j = a i j + a j i := by
    intro i j; simp only [ha, hB]
    by_cases h : G.Adj i j
    · have h' : G.Adj j i := h.symm
      rw [if_pos h, if_pos h, if_pos h']; ring
    · have h' : ¬ G.Adj j i := fun x => h x.symm
      rw [if_neg h, if_neg h, if_neg h']; ring
  have hswap : (∑ i : V, ∑ j : V, a i j) = ∑ i : V, ∑ j : V, a j i := Finset.sum_comm
  have hBsum : (∑ i : V, ∑ j : V, B i j)
      = (∑ i : V, ∑ j : V, a i j) + (∑ i : V, ∑ j : V, a j i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hpt i j
  rw [← hswap] at hBsum
  linarith [hBsum]

/-- **Degree-weighted summation-by-parts identity (spectral).** Multiplying the row equation
`A f = (D−lam) f` by the degree-weighted multiplier `d_v f_v` and summing:
`(D f)ᵀ(A f) = Σ_v d_v (d_v − lam) f_v²`, equivalently `Σ_{ab∈E}(d_a+d_b)f_a f_b
= Σ_v d_v(d_v−lam)f_v²`. The `w = d` member of the edge↔diagonal SBP family
(`informal/conjecture_B_global_summation_parts.md`): it converts a degree-weighted *edge*
correlation into a degree *diagonal*, with the eigenvalue entering linearly. -/
lemma quadForm_deg_adjMatrix_fiedler (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    dotProduct ((G.degMatrix ℝ).mulVec f) ((G.adjMatrix ℝ).mulVec f)
      = ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - lam) * (f v) ^ 2 := by
  have hA := adjMatrix_mulVec_fiedler G f lam heig
  have hDf : (G.degMatrix ℝ).mulVec f = fun v => (G.degree v : ℝ) * f v := by
    funext v; simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]
  rw [hA, hDf]
  simp only [dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- **Neighbourhood variance (Dirichlet) identity (algebraic, no spectral hypothesis).** Over the
neighbours of any apex `c`, the full ordered Dirichlet energy is
`Σ_{a,b∈N(c)}(f_a−f_b)² = 2·d_c·(Σ_{v∈N(c)} f_v²) − 2·(Σ_{v∈N(c)} f_v)²`. The per-apex building
block of the open-2-path / triangle energy split (`informal/conjecture_B_open_apex_pairing.md`):
splitting the pair sum by adjacency gives `Open_c + T_c` on the left, and with the eigen-recursion
`Σ_{v∈N(c)} f_v = (d_c−λ₂)f_c` the right side becomes `2 d_c·mass_c − 2(d_c−λ₂)² f_c²`. -/
lemma neighbor_dirichlet_identity (f : V → ℝ) (c : V) :
    ∑ a ∈ G.neighborFinset c, ∑ b ∈ G.neighborFinset c, (f a - f b) ^ 2
      = 2 * (G.degree c : ℝ) * (∑ v ∈ G.neighborFinset c, (f v) ^ 2)
        - 2 * (∑ v ∈ G.neighborFinset c, f v) ^ 2 := by
  set S := G.neighborFinset c with hS
  have hcard : (S.card : ℝ) = (G.degree c : ℝ) := by
    rw [hS, SimpleGraph.card_neighborFinset_eq_degree]
  have hP1 : (∑ a ∈ S, ∑ _b ∈ S, (f a) ^ 2) = (S.card : ℝ) * ∑ v ∈ S, (f v) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hP2 : (∑ _a ∈ S, ∑ b ∈ S, (f b) ^ 2) = (S.card : ℝ) * ∑ v ∈ S, (f v) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hP3 : (∑ a ∈ S, ∑ b ∈ S, f a * f b) = (∑ v ∈ S, f v) ^ 2 := by
    rw [← Finset.sum_mul_sum, pow_two]
  have hsplit : (∑ a ∈ S, ∑ b ∈ S, (f a - f b) ^ 2)
      = (∑ a ∈ S, ∑ b ∈ S, (f a) ^ 2) + (∑ a ∈ S, ∑ b ∈ S, (f b) ^ 2)
        - 2 * (∑ a ∈ S, ∑ b ∈ S, f a * f b) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsplit, hP1, hP2, hP3, hcard]; ring

/-- **Carré-du-champ product rule for the graph Laplacian (algebraic, no spectral hypothesis).**
`(L(f∘f))_v = 2·f_v·(Lf)_v − Σ_{u∼v}(f_v−f_u)²`, i.e. `L(f²) = 2 f·Lf − 2Γ(f)` with the Bakry–Émery
carré du champ `Γ(f)(v) = ½Σ_{u∼v}(f_v−f_u)²`. At a Laplacian eigenvector (`Lf = λ₂·f`) this is the
eigenfunction Bochner identity `L(f²) = 2λ₂·f² − 2Γ(f)`, which (degree-averaged) recasts the
covariance correction as a carré du champ: `𝒜 = Cov_L(d,f²) = 2λ₂·fᵀDf − 2⟨d,Γ(f)⟩`
(`informal/conjecture_B_bochner_open_paths.md`). -/
lemma lapMatrix_mulVec_sq (f : V → ℝ) (v : V) :
    (G.lapMatrix ℝ).mulVec (fun w => (f w) ^ 2) v
      = 2 * f v * ((G.lapMatrix ℝ).mulVec f v)
        - ∑ u : V, if G.Adj v u then (f v - f u) ^ 2 else 0 := by
  have hrow : ∀ (g : V → ℝ) (x : V), ((G.lapMatrix ℝ).mulVec g) x
      = ∑ u : V, if G.Adj x u then (g x - g u) else 0 := by
    intro g x
    have hLDA : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
    rw [hLDA, Matrix.sub_mulVec, Pi.sub_apply]
    rw [show (G.degMatrix ℝ).mulVec g x = (G.degree x : ℝ) * g x from by
      simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]]
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [show (∑ u : V, if G.Adj x u then (g x - g u) else 0)
        = ∑ u ∈ G.neighborFinset x, (g x - g u) from by
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]]
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul]
  rw [hrow (fun w => (f w) ^ 2) v, hrow f v, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : G.Adj v u
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- **Zero column-sum of the graph Laplacian (algebraic).** `Σ_v (L g)_v = 0` for any `g`
(`L = D − A`; the Dirichlet form `Σ_{i,j}[i∼j](g_i−g_j)` is antisymmetric). This is the engine of
the integrated Bochner identity: with the carré du champ `Γ(f)` (`Σ_v Γ(f)(v) = fᵀLf`) and
`Γ₂(f) = ½·L Γ(f) − λ₂·Γ(f)` (eigenvector), it gives `Σ_v Γ₂(f)(v) = −λ₂·Σ_v Γ(f)(v) = −λ₂²`
(`informal/conjecture_B_weighted_bochner.md`). -/
lemma lapMatrix_mulVec_sum_zero (g : V → ℝ) :
    ∑ v : V, (G.lapMatrix ℝ).mulVec g v = 0 := by
  have hrow : ∀ (x : V), ((G.lapMatrix ℝ).mulVec g) x
      = ∑ u : V, if G.Adj x u then (g x - g u) else 0 := by
    intro x
    have hLDA : G.lapMatrix ℝ = G.degMatrix ℝ - G.adjMatrix ℝ := rfl
    rw [hLDA, Matrix.sub_mulVec, Pi.sub_apply]
    rw [show (G.degMatrix ℝ).mulVec g x = (G.degree x : ℝ) * g x from by
      simp [SimpleGraph.degMatrix, Matrix.mulVec_diagonal]]
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [show (∑ u : V, if G.Adj x u then (g x - g u) else 0)
        = ∑ u ∈ G.neighborFinset x, (g x - g u) from by
      rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]]
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
        nsmul_eq_mul]
  simp_rw [hrow]
  set a : V → V → ℝ := fun v u => if G.Adj v u then (g v - g u) else 0 with ha
  have hanti : ∀ v u : V, a u v = - a v u := by
    intro v u; simp only [ha]
    by_cases h : G.Adj v u
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (fun x => h x.symm)]; ring
  have h1 : (∑ v : V, ∑ u : V, a v u) = ∑ v : V, ∑ u : V, a u v := Finset.sum_comm
  have h2 : (∑ v : V, ∑ u : V, a u v) = - ∑ v : V, ∑ u : V, a v u := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun u _ => hanti v u
  linarith [h1, h2]

/-- **Weighted-Laplacian quadratic form / sum-of-squares (algebraic).** For any *symmetric* weight
matrix `W`, the `W`-Dirichlet energy is `Σ_{i,j} W_ij (f_i−f_j)² = 2[Σ_i (Σ_j W_ij) f_i² −
Σ_{i,j} W_ij f_i f_j]`, i.e. `fᵀ(diag(rowSum W) − W)f = ½ Σ_{i,j} W_ij (f_i−f_j)²`. Specialising
`W = P` (the open-2-path operator `P_ab = #common nbrs with a≁b`) gives the manifest sum-of-squares
`Open = fᵀL_P f = Σ_{a<b} P_ab (f_a−f_b)²`, i.e. `L_P = B_openᵀ B_open` with one row per open
cherry (`informal/conjecture_B_open2path_operator.md`). No spectral hypothesis. -/
lemma quadForm_weighted_laplacian (W : Matrix V V ℝ) (hsymm : ∀ i j : V, W i j = W j i)
    (f : V → ℝ) :
    ∑ i : V, ∑ j : V, W i j * (f i - f j) ^ 2
      = 2 * (∑ i : V, (∑ j : V, W i j) * (f i) ^ 2)
        - 2 * (∑ i : V, ∑ j : V, W i j * (f i * f j)) := by
  have hpull : ∀ i : V, (∑ j : V, W i j * (f i) ^ 2) = (∑ j : V, W i j) * (f i) ^ 2 := by
    intro i; rw [Finset.sum_mul]
  have hsymm2 : (∑ i : V, ∑ j : V, W i j * (f j) ^ 2)
      = ∑ i : V, ∑ j : V, W i j * (f i) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm b a]
  have hexp : ∀ i j : V, W i j * (f i - f j) ^ 2
      = W i j * (f i) ^ 2 + W i j * (f j) ^ 2 - 2 * (W i j * (f i * f j)) := fun i j => by ring
  calc (∑ i : V, ∑ j : V, W i j * (f i - f j) ^ 2)
      = (∑ i : V, ∑ j : V, W i j * (f i) ^ 2) + (∑ i : V, ∑ j : V, W i j * (f j) ^ 2)
          - 2 * (∑ i : V, ∑ j : V, W i j * (f i * f j)) := by
        simp_rw [hexp]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (∑ i : V, (∑ j : V, W i j) * (f i) ^ 2)
          - 2 * (∑ i : V, ∑ j : V, W i j * (f i * f j)) := by
        rw [hsymm2, ← two_mul]
        have hrw : (∑ i : V, ∑ j : V, W i j * (f i) ^ 2)
            = ∑ i : V, (∑ j : V, W i j) * (f i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => hpull i
        rw [hrw]

/-- **Adjacency column-sum / weighted handshake (algebraic).** `Σ_v (A f)_v = Σ_v d_v f_v`, i.e.
`1ᵀ A f = S` (`S = Σ_v d_v f_v`). With `1ᵀ D f = S` this gives `1ᵀ(D+A)f = 2S` — the off-diagonal
`⟨u₁, (λ₂Q − L_M) u₂⟩ = λ₂·2S/√n` of the 2×2 low-frequency `{const, Fiedler}` block of
`M = λ₂Q − L_M`, whose positive-semidefiniteness is exactly Conjecture B; the `S²` it contributes is
the `S²/m` correction of the lift bound (`informal/conjecture_B_spectral_orthogonality.md`).
No spectral hypothesis. -/
lemma adjMatrix_mulVec_sum (f : V → ℝ) :
    ∑ v : V, (G.adjMatrix ℝ).mulVec f v = ∑ u : V, (G.degree u : ℝ) * f u := by
  have hrow : ∀ v : V, (G.adjMatrix ℝ).mulVec f v
      = ∑ u : V, if G.Adj v u then f u else 0 := by
    intro v
    rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hfac : (∑ v : V, if G.Adj v u then f u else 0)
      = (∑ v : V, if G.Adj v u then (1 : ℝ) else 0) * f u := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : G.Adj v u <;> simp [h]
  rw [hfac]
  have hcnt : (∑ v : V, if G.Adj v u then (1 : ℝ) else 0) = (G.degree u : ℝ) := by
    rw [Finset.sum_boole]
    rw [show (Finset.univ.filter (fun v => G.Adj v u)) = G.neighborFinset u from by
      ext v; simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]]
    rw [SimpleGraph.card_neighborFinset_eq_degree]
  rw [hcnt]

/-- **Lagrange identity (Gram determinant = sum of squares).** For any `a, b : ι → ℝ`,
`(Σ aᵢ²)(Σ bᵢ²) − (Σ aᵢbᵢ)² = ½ Σ_{i,j}(aᵢbⱼ − aⱼbᵢ)²` — the Cauchy–Schwarz/Gram-determinant gap as
a manifest sum of squares. Specialising `a = h` (edge-lift `hₑ = f_a+f_b`), `b = 1` gives the
manifestly-nonnegative part of the determinant `det(M_low) = (4λ₂/n)(λ₂·G − m·T)`, namely
`G = m·fᵀQf − S² = ½ Σ_{e,e'}(hₑ − h_{e'})² = m²·Var_E(h) ≥ 0`
(`informal/conjecture_B_determinant_form.md`). -/
lemma lagrange_identity {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i : ι, (a i) ^ 2) * (∑ i : ι, (b i) ^ 2) - (∑ i : ι, a i * b i) ^ 2
      = (1 / 2) * ∑ i : ι, ∑ j : ι, (a i * b j - a j * b i) ^ 2 := by
  have hAA : (∑ i : ι, ∑ j : ι, (a i) ^ 2 * (b j) ^ 2)
      = (∑ i : ι, (a i) ^ 2) * (∑ j : ι, (b j) ^ 2) := by
    rw [← Finset.sum_mul_sum]
  have hBB : (∑ i : ι, ∑ j : ι, (a j) ^ 2 * (b i) ^ 2)
      = (∑ i : ι, (a i) ^ 2) * (∑ j : ι, (b j) ^ 2) := by
    rw [Finset.sum_comm, ← Finset.sum_mul_sum]
  have hAB : (∑ i : ι, ∑ j : ι, 2 * ((a i * b i) * (a j * b j)))
      = 2 * ((∑ i : ι, a i * b i) * (∑ j : ι, a j * b j)) := by
    have h2 : (∑ i : ι, ∑ j : ι, 2 * ((a i * b i) * (a j * b j)))
        = 2 * ∑ i : ι, ∑ j : ι, (a i * b i) * (a j * b j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    rw [h2, ← Finset.sum_mul_sum]
  have hsplit : (∑ i : ι, ∑ j : ι, (a i * b j - a j * b i) ^ 2)
      = (∑ i : ι, ∑ j : ι, (a i) ^ 2 * (b j) ^ 2)
        + (∑ i : ι, ∑ j : ι, (a j) ^ 2 * (b i) ^ 2)
        - (∑ i : ι, ∑ j : ι, 2 * ((a i * b i) * (a j * b j))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hAA, hBB, hAB]; ring

/-- **Aggregate triangle-Poincaré (OPEN).** `T ≤ λ₂·fᵀDf` (ordered: `T_ord ≤ 2λ₂·fᵀDf`).

This is `Σ_c E_{G[N(c)]}(f) ≤ λ₂·Σ_c (Σ_{v∈N(c)} f_v²)` summed via the apex identity
(`apex_triangle_energy_identity`, `Paper15`). The *local* Poincaré
`E_{G[N(c)]}(f) ≤ λ₂·Σ_{N(c)}f²` fails on ~6% of apices, but the aggregate holds on every
tested graph (0 violations). Proof path open. -/
lemma aggregate_triangle_poincare (f : V → ℝ) (lam : ℝ)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    triEnergy G f ≤ 2 * lam * degQuad G f := by
  sorry

/-- **Regime (ii): `Required > 0` (OPEN).** The bottleneck regime. Empirically the slack
`Deficit − Required = RHS − T` stays positive with `Deficit/Required ≥ 1.7`; no closed-form
proof yet (every edge/apex-local bound is either invalid on the bottleneck edges or too
loose on the dense edges — see the `informal/` analyses). -/
lemma conjectureB_regime_two (f : V → ℝ) (lam mE : ℝ) (hmE : 0 < mE) (hlam : 0 < lam)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f)
    (hReq : degQuad G f < lam + (degLin G f) ^ 2 / mE) :
    triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := by
  sorry

/-- **Conjecture B — triangle-energy lift inequality.** For a unit Fiedler vector `f`
(`L_G f = λ₂ f`, `λ₂ > 0`) and `mE = |E| > 0`:
`T ≤ λ₂·(fᵀQf − S²/m)`, ordered form `T_ord ≤ 2λ₂(2fᵀDf − λ₂ − S²/mE)`.

This implies `λ₂(T(G)) ≤ λ₂(G)` (Conjecture B) via the projected Fiedler lift. Proof: a
regime split on `sign(Required)`; **regime (i) is closed** here (modulo the aggregate
Poincaré), regime (ii) is the open lemma. -/
theorem conjectureB_lift (f : V → ℝ) (lam mE : ℝ) (hmE : 0 < mE) (hlam : 0 < lam)
    (heig : (G.lapMatrix ℝ).mulVec f = lam • f) :
    triEnergy G f ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) := by
  by_cases hReq : lam + (degLin G f) ^ 2 / mE - degQuad G f ≤ 0
  · -- Regime (i): Required ≤ 0  ⇒  fᵀDf ≥ λ₂ + S²/m  ⇒  fᵀQf − S²/m ≥ fᵀDf.
    have hpoin := aggregate_triangle_poincare G f lam heig
    calc triEnergy G f
        ≤ 2 * lam * degQuad G f := hpoin
      _ ≤ 2 * lam * (2 * degQuad G f - lam - (degLin G f) ^ 2 / mE) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  · -- Regime (ii): Required > 0.
    push_neg at hReq
    exact conjectureB_regime_two G f lam mE hmE hlam heig (by linarith)

/-- **Conjecture B (graph statement).** For connected `G` with `T(G)` connected,
`λ₂(T(G)) ≤ λ₂(G)`. Reduces to `conjectureB_lift` via the projected Fiedler lift
`h' = Bᵀf − (S/m)1_E ⊥ 1_E` together with `t_ab ≤ min(d_a,d_b)−1`
(`triCount_le_min_degree_sub_one`); that lift reduction is not yet formalised. -/
theorem conjectureB (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (hTV : Fintype.card (G.edgeSet) ≥ 2) (hTconn : (triangleGraph G).Connected) :
    algebraicConnectivity (triangleGraph G) hTV ≤ algebraicConnectivity G hV := by
  sorry

end Topostability
