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

/-- The triangle graph T(G): vertices are edges of G (elements of `G.edgeSet`),
two edges are adjacent iff they share an endpoint and the three vertices
form a triangle in G. -/
def triangleGraph : SimpleGraph G.edgeSet where
  Adj e₁ e₂ := ∃ (u v w : V), e₁.val = s(u, v) ∧ e₂.val = s(u, w) ∧ G.Adj v w
  symm e₁ e₂ := by
    rintro ⟨u, v, w, h1, h2, hadj⟩
    exact ⟨u, w, v, h2, h1, hadj.symm⟩
  loopless := ⟨fun e => by
    rintro ⟨u, v, w, h1, h2, hadj⟩
    have heq : s(u, v) = s(u, w) := h1.symm.trans h2
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨-, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hadj.ne rfl⟩

noncomputable instance triangleGraph.instDecidableRel :
    DecidableRel (triangleGraph G).Adj :=
  fun _ _ => Classical.dec _

end Topostability
