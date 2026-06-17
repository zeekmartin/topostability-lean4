import Topostability.Defs
import Topostability.Shared
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Apex triangle-energy identity (ordered form).**

The triangle-weighted Dirichlet energy equals the sum, over apex vertices `c`, of the
Dirichlet energies on the neighbourhoods `G[N(c)]`:

`∑_{i,j} [i~j] · |N(i)∩N(j)| · (f_i − f_j)²
  = ∑_c ∑_{i,j} [i∈N(c) ∧ j∈N(c) ∧ i~j] · (f_i − f_j)²`.

Both sides are written as ordered double sums over `V × V` (each undirected edge counted
twice, matching `SimpleGraph.lapMatrix_toLinearMap₂'`), so this is exactly `∑_{ab∈E}
|N(a)∩N(b)|(f_a−f_b)² = ∑_c ∑_{ab∈E(G[N(c)])}(f_a−f_b)²` after dividing both sides by 2.

Pure double-counting: each adjacent pair `(i,j)` contributes `(f_i−f_j)²` once per common
neighbour `c`, and `c` is a common neighbour iff both `i,j ∈ N(c)`. Proof = swap the order
of summation (`Finset.sum_comm`) after writing `|N(i)∩N(j)|` as `∑_c [i∈N(c) ∧ j∈N(c)]`. -/
theorem apex_triangle_energy_identity (f : V → ℝ) :
    (∑ i : V, ∑ j : V, if G.Adj i j then
        ((G.neighborFinset i ∩ G.neighborFinset j).card : ℝ) * (f i - f j) ^ 2 else 0)
    = ∑ c : V, ∑ i : V, ∑ j : V,
        if (i ∈ G.neighborFinset c ∧ j ∈ G.neighborFinset c ∧ G.Adj i j)
          then (f i - f j) ^ 2 else 0 := by
  -- the common neighbours of `i,j` are exactly the `c` with `i,j ∈ N(c)`
  have count : ∀ i j : V,
      (Finset.univ.filter (fun c => i ∈ G.neighborFinset c ∧ j ∈ G.neighborFinset c))
        = G.neighborFinset i ∩ G.neighborFinset j := by
    intro i j; ext c
    constructor
    · intro hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset] at hc
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨(G.adj_comm c i).mp hc.1, (G.adj_comm c j).mp hc.2⟩
    · intro hc
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨(G.adj_comm i c).mp hc.1, (G.adj_comm j c).mp hc.2⟩
  -- swap the apex sum to the inside (only on the RHS)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- per `(i,j)`: ∑_c [i,j∈N(c) ∧ i~j] (f_i−f_j)² = [i~j]·|N(i)∩N(j)|·(f_i−f_j)²
  split_ifs with hadj
  · simp only [hadj, and_true]
    rw [← Finset.sum_filter, Finset.sum_const, count i j, nsmul_eq_mul]
  · symm
    exact Finset.sum_eq_zero fun c _ => if_neg (fun h => hadj h.2.2)

end Topostability
