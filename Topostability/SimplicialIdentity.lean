/-
GAP #4 — Lean 4 — Simplicial Identity Theorem (v8)
tri(e) = |{σ ∈ K₂(G) : e ⊂ σ}|

Fixes from Gemini review:
  1. card_sdiff_add_card_inter (avoids ℕ subtraction pitfall)
     #(s \ t) + #(s ∩ t) = #s  →  no subtraction on ℕ
  2. Finset.eq_of_subset_of_card_le (stable name in current Mathlib)
     instead of eq_of_subset_of_card_eq (unknown)
  3. obtain pattern for hK2: flat ⟨-, hcard, hclique⟩

Author: David Martin Venti — Cognitive Engineering — 22 March 2026
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- ─────────────────────────────────────────────────────────────────
-- 1.  DEFINITIONS
-- ─────────────────────────────────────────────────────────────────

def triCount (u v : V) : ℕ :=
  (G.neighborFinset u ∩ G.neighborFinset v).card

def K2 (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.powerset.filter (fun s => s.card = 3 ∧ G.IsClique s)

def simplicialStar (u v : V) : Finset (Finset V) :=
  (K2 G).filter (fun σ => {u, v} ⊆ σ)

-- ─────────────────────────────────────────────────────────────────
-- 2.  AUXILIARY
-- ─────────────────────────────────────────────────────────────────

omit [Fintype V] in
lemma card_triple (u v w : V) (h1 : u ≠ v) (h2 : u ≠ w) (h3 : v ≠ w) :
    ({u, v, w} : Finset V).card = 3 := by
  rw [Finset.card_eq_three]; exact ⟨u, v, w, h1, h2, h3, rfl⟩

-- ─────────────────────────────────────────────────────────────────
-- 3.  BIJECTION LEMMAS
-- ─────────────────────────────────────────────────────────────────

lemma commonNeigh_to_K2 (u v w : V)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (h1 : u ≠ v) (h2 : u ≠ w) (h3 : v ≠ w) :
    ({u, v, w} : Finset V) ∈ K2 G := by
  simp only [K2, mem_filter, mem_powerset, subset_univ, true_and]
  refine ⟨card_triple u v w h1 h2 h3, ?_⟩
  intro x hx y hy hne
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff,
             Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hne
    | exact huv | exact huv.symm
    | exact huw | exact huw.symm
    | exact hvw | exact hvw.symm

lemma commonNeigh_to_star (u v w : V)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    (h1 : u ≠ v) (h2 : u ≠ w) (h3 : v ≠ w) :
    ({u, v, w} : Finset V) ∈ simplicialStar G u v := by
  simp only [simplicialStar, mem_filter]
  exact ⟨commonNeigh_to_K2 G u v w huv huw hvw h1 h2 h3,
         by simp [Finset.insert_subset_iff]⟩

-- ─────────────────────────────────────────────────────────────────
-- 4.  MAIN THEOREM
-- ─────────────────────────────────────────────────────────────────

theorem simplicial_identity (u v : V) (huv : G.Adj u v) (h : u ≠ v) :
    triCount G u v = (simplicialStar G u v).card := by
  apply Finset.card_bij (fun w _ => ({u, v, w} : Finset V))
  -- (a) typing
  · intro w hw
    simp only [mem_inter, G.mem_neighborFinset] at hw
    obtain ⟨huw, hvw⟩ := hw
    exact commonNeigh_to_star G u v w huv huw hvw h
      (G.ne_of_adj huw) (G.ne_of_adj hvw)
  -- (b) injectivity
  · intro w₁ hw₁ w₂ _ heq
    simp only [mem_inter, G.mem_neighborFinset] at hw₁
    have hmem : w₁ ∈ ({u, v, w₂} : Finset V) := by rw [← heq]; simp
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact absurd rfl (G.ne_of_adj hw₁.1)
    · exact absurd rfl (G.ne_of_adj hw₁.2)
    · rfl
  -- (c) surjectivity
  · intro σ hσ
    simp only [simplicialStar, mem_filter] at hσ
    obtain ⟨hK2, hcontains⟩ := hσ
    simp only [K2, mem_filter, mem_powerset] at hK2
    -- FIX v7: flat triple, use - to discard σ ⊆ univ
    obtain ⟨-, hcard, hclique⟩ := hK2
    -- FIX 1: avoid ℕ subtraction — use additive identity instead
    -- Finset.card_sdiff_add_card_inter : #(σ \ {u,v}) + #(σ ∩ {u,v}) = #σ
    have h_uv_card : ({u, v} : Finset V).card = 2 := Finset.card_pair h
    have h_sdiff_card : (σ \ {u, v}).card = 1 := by
      have h_sum := Finset.card_sdiff_add_card_inter σ {u, v}
      rw [Finset.inter_eq_right.mpr hcontains, hcard, h_uv_card] at h_sum
      -- h_sum : #(σ \ {u,v}) + 2 = 3
      omega
    -- bring w into scope
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h_sdiff_card
    -- extract membership
    have hmem_sdiff : w ∈ σ \ {u, v} := by rw [hw]; exact mem_singleton_self w
    have hw_in_σ  : w ∈ σ             := (mem_sdiff.mp hmem_sdiff).1
    have hw_not_uv : w ∉ ({u, v} : Finset V) := (mem_sdiff.mp hmem_sdiff).2
    have h2 : u ≠ w := by intro heq; exact hw_not_uv (by simp [heq])
    have h3 : v ≠ w := by intro heq; exact hw_not_uv (by simp [heq])
    -- FIX 2: eq_of_subset_of_card_le (stable name)
    have hσ_eq : σ = {u, v, w} := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert, mem_singleton]
        by_cases hxu : x = u; · left; exact hxu
        by_cases hxv : x = v; · right; left; exact hxv
        right; right
        have : x ∈ σ \ {u, v} := by simp [mem_sdiff, hx, hxu, hxv]
        rwa [hw, mem_singleton] at this
      · rw [card_triple u v w h h2 h3, hcard]
    -- adjacency from clique
    have huw : G.Adj u w := hclique (hcontains (by simp)) hw_in_σ h2
    have hvw : G.Adj v w := hclique (hcontains (by simp)) hw_in_σ h3
    exact ⟨w, by simp [mem_inter, G.mem_neighborFinset, huw, hvw],
           hσ_eq.symm⟩

-- ─────────────────────────────────────────────────────────────────
-- 5.  COROLLARIES
-- ─────────────────────────────────────────────────────────────────

theorem corollary_A (u v : V) (huv : G.Adj u v) (h : u ≠ v)
    (htau : 0 < triCount G u v) :
    (simplicialStar G u v).Nonempty :=
  Finset.card_pos.mp (by rwa [← simplicial_identity G u v huv h])

theorem corollary_B (u v : V) (huv : G.Adj u v) (h : u ≠ v)
    (htau : triCount G u v = 0) :
    simplicialStar G u v = ∅ := by
  rw [← Finset.card_eq_zero, ← simplicial_identity G u v huv h]
  exact htau