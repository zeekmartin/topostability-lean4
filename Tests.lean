import Topostability.Conjectures

namespace Topostability

-- ══════════════════════════════════════════════════════
-- TEST 1: Axiom check
-- Theorems proved without sorry show only: propext, Classical.choice, Quot.sound
-- Theorems depending on sorry show `sorry` in axioms
-- ══════════════════════════════════════════════════════

-- Paper 13 main theorem (should be sorry-free now!)
#print axioms lambda2_triangle_graph_le

-- Helper lemmas (should be clean)
#print axioms triangleGraph_quadratic_form
#print axioms triangleGraph_quadratic_bound
#print axioms edgeLift_sum_regular
#print axioms edgeLift_norm_fiedler
#print axioms edgeLift_sum_zero
#print axioms edgeLift_triangleAdj_sq
#print axioms edgeLift_mk

-- Paper 11 (has sorry from htrace_eq/hA2_trace)
#print axioms spectral_identity

-- ══════════════════════════════════════════════════════
-- TEST 2: Type-checking the theorem application
-- Verify all types/instances align for a concrete graph
-- ══════════════════════════════════════════════════════

-- The theorem typechecks with abstract hypotheses
example {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hV : Fintype.card V ≥ 2)
    (d : ℕ) (hreg : G.IsRegularOfDegree d) (hd : 2 ≤ d)
    (hV' : Fintype.card G.edgeSet ≥ 2)
    (hTconn : (triangleGraph G).Connected) :
    algebraicConnectivity (triangleGraph G) hV' ≤ algebraicConnectivity G hV :=
  lambda2_triangle_graph_le G hconn hV d hreg hd hV' hTconn

-- ══════════════════════════════════════════════════════
-- TEST 3: Verify triangleGraph definition
-- For K₃ (complete graph on 3 vertices):
-- - G has 3 edges
-- - T(G) has 3 vertices (= edges of G)
-- - Each pair of edges shares a vertex and forms a triangle
-- ══════════════════════════════════════════════════════

-- Verify edgeLift computation rule
example {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    {u v : W} (h : s(u, v) ∈ G.edgeSet) (f : W → ℝ) :
    edgeLift G f ⟨s(u, v), h⟩ = f u + f v :=
  edgeLift_mk G f h

end Topostability
