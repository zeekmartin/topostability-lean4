import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Defs

namespace Topostability

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of common neighbors between `u` and `v`. -/
def triCount (u v : V) : ℕ :=
  (G.neighborFinset u ∩ G.neighborFinset v).card

/-- An edge is always fragile if it has no common neighbors. -/
def alwaysFragile (u v : V) : Bool :=
  triCount G u v == 0

/-- Lift `triCount` to `Sym2 V` (unordered pairs). -/
def triCountSym2 (e : Sym2 V) : ℕ :=
  Sym2.lift ⟨triCount G, fun _ _ => by simp [triCount, Finset.inter_comm]⟩ e

/-- Minimum `triCount` over all edges of `G`. Returns 0 if `G` has no edges. -/
def tauG : ℕ :=
  if h : G.edgeFinset.Nonempty then
    G.edgeFinset.inf' h (triCountSym2 G)
  else 0

/-- Total number of triangles in `G`, i.e., the number of 3-cliques. -/
def totalTriangles : ℕ :=
  (G.cliqueFinset 3).card

/-- Proportion of edges that are always fragile (have `triCount = 0`). -/
noncomputable def fragilityIndex : ℚ :=
  if G.edgeFinset.card = 0 then 0
  else ↑(G.edgeFinset.filter (fun e => triCountSym2 G e == 0)).card / ↑G.edgeFinset.card

end Topostability
