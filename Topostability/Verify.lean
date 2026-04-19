import Topostability.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant

open Topostability SimpleGraph

/-- K3: complete graph on 3 vertices. -/
abbrev K3 : SimpleGraph (Fin 3) := ⊤

/-- K4: complete graph on 4 vertices. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

/-- P3: path graph on 3 vertices (0 — 1 — 2). -/
def P3 : SimpleGraph (Fin 3) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm _ _ h := h.symm
  loopless := ⟨fun _ h => by omega⟩

instance : DecidableRel P3.Adj :=
  fun i j => inferInstanceAs (Decidable ((i.val + 1 = j.val) ∨ (j.val + 1 = i.val)))

/-- C4: cycle graph on 4 vertices. -/
abbrev C4 : SimpleGraph (Fin 4) := cycleGraph 4

-- tauG computations
#eval tauG K3          -- expected: 1
#eval tauG K4          -- expected: 2
#eval tauG P3          -- expected: 0
#eval tauG C4          -- expected: 0

-- C4 counterexample: connected, tauG = 0, but every edge has triCount = 0
-- yet C4 has NO bridges (it's a cycle). This refutes exists_bridge_of_tauG_eq_zero.
#eval (triCount C4 0 1, triCount C4 1 2, triCount C4 2 3, triCount C4 0 3)
  -- expected: (0, 0, 0, 0) — all edges are fragile, but none are bridges

-- totalTriangles computations
#eval totalTriangles K3  -- expected: 1
#eval totalTriangles K4  -- expected: 4
#eval totalTriangles P3  -- expected: 0
#eval totalTriangles C4  -- expected: 0
