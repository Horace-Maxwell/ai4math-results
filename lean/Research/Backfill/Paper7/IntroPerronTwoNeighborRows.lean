import Mathlib

/-! Complete degree-three neighborhoods and exact two-neighbor row erasure.
All statements concern the actual adjacency matrix and finite neighborhoods. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeLeafSuccessors
open SimpleGraph Matrix

theorem degree_three_neighbor_finset
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c a u v : V)
    (hd : G.degree c = 3) (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v)
    (hca : G.Adj c a) (hcu : G.Adj c u) (hcv : G.Adj c v) :
    G.neighborFinset c = {a, u, v} := by
  have hsub : ({a, u, v} : Finset V) ⊆ G.neighborFinset c := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact (G.mem_neighborFinset c a).mpr hca
    · rw [hx]
      exact (G.mem_neighborFinset c u).mpr hcu
    · rw [hx]
      exact (G.mem_neighborFinset c v).mpr hcv
  have haUV : a ∉ ({u, v} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hau, hav⟩
  have hcard : ({a, u, v} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem haUV, Finset.card_pair huv]
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [G.card_neighborFinset_eq_degree, hd, hcard]
#print axioms Paper7IntroThreeLeafSuccessors.degree_three_neighbor_finset

theorem eigen_three_two_neighbor_erase_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ)
    (hAf : G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f)
    (x y z : V) (hyz : y ≠ z) (hxy : G.Adj x y) (hxz : G.Adj x z) :
    (∑ t ∈ ((G.neighborFinset x).erase y).erase z, f t) + f z + f y =
      3 * f x := by
  have hyN : y ∈ G.neighborFinset x := (G.mem_neighborFinset x y).mpr hxy
  have hzN : z ∈ (G.neighborFinset x).erase y :=
    Finset.mem_erase.mpr ⟨hyz.symm, (G.mem_neighborFinset x z).mpr hxz⟩
  have h1 := Finset.sum_erase_add (G.neighborFinset x) f hyN
  have h2 := Finset.sum_erase_add ((G.neighborFinset x).erase y) f hzN
  have hrow : (∑ t ∈ G.neighborFinset x, f t) = 3 * f x := by
    simpa only [G.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] using congrFun hAf x
  linarith only [h1, h2, hrow]
#print axioms Paper7IntroThreeLeafSuccessors.eigen_three_two_neighbor_erase_sum

end Paper7IntroThreeLeafSuccessors
