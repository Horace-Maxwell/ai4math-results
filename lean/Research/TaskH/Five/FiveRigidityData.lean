import Research.TaskH.Five.FivePatternData

/-!
Literal five-position reindexings for extra star and gem edges, and the
cross-edge tables for pairs in each forced-color group. These are finite
identities; transport to actual graph vertices belongs to a separate module.
-/

set_option autoImplicit false

namespace TaskH.Five

open SimpleGraph

theorem star_extra_reindex (i j : Fin 5) (hne : i ≠ j)
    (hex : s(i, j) ∉ patternStar) :
    ∃ r : Fin 5 → Fin 5, Function.Injective r ∧
      ∀ a b : Fin 5, s(a, b) ∈ patternNearComplete →
        s(r a, r b) ∈ insert (s(i, j)) patternStar := by
  have hclass : ∀ a b : Fin 5, a ≠ b → s(a, b) ∉ patternStar →
      (a = 2 ∧ b = 4) ∨ (a = 4 ∧ b = 2) ∨
        (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) := by
    decide +kernel
  rcases hclass i j hne hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨![3, 4, 0, 1, 2], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel
  · refine ⟨![3, 4, 0, 1, 2], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel
  · refine ⟨![2, 4, 0, 1, 3], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel
  · refine ⟨![2, 4, 0, 1, 3], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel

theorem gem_extra_reindex (i j : Fin 5) (hne : i ≠ j)
    (hex : s(i, j) ∉ patternGem) :
    (∃ r : Fin 5 → Fin 5, Function.Injective r ∧
      ∀ a b : Fin 5, s(a, b) ∈ patternMissingMatching →
        s(r a, r b) ∈ insert (s(i, j)) patternGem) ∨
    (∃ r : Fin 5 → Fin 5, Function.Injective r ∧
      ∀ a b : Fin 5, s(a, b) ∈ patternStar →
        s(r a, r b) ∈ insert (s(i, j)) patternGem) := by
  have hclass : ∀ a b : Fin 5, a ≠ b → s(a, b) ∉ patternGem →
      (a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0) ∨
        (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨
        (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) := by
    decide +kernel
  rcases hclass i j hne hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    refine ⟨![0, 2, 1, 3, 4], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel
  · left
    refine ⟨![0, 2, 1, 3, 4], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel
  · right
    refine ⟨![2, 4, 0, 1, 3], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel
  · right
    refine ⟨![2, 4, 0, 1, 3], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel
  · right
    refine ⟨![1, 4, 2, 3, 0], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel
  · right
    refine ⟨![1, 4, 2, 3, 0], ?_, ?_⟩
    · unfold Function.Injective
      decide +kernel
    · decide +kernel

theorem star_pairs_cross (I J : Finset (Fin 5))
    (hI : I = {0, 1} ∨ I = {2, 3})
    (hJ : J = {0, 1} ∨ J = {2, 3}) :
    ∃ i ∈ I, ∃ j ∈ J, s(i, j) ∈ patternStar := by
  rcases hI with rfl | rfl <;> rcases hJ with rfl | rfl <;> decide +kernel

theorem gem_left_pairs_cross (I J : Finset (Fin 5))
    (hI : I = {4, 1} ∨ I = {4, 3} ∨ I = {2, 3})
    (hJ : J = {4, 1} ∨ J = {4, 3} ∨ J = {2, 3}) :
    ∃ i ∈ I, ∃ j ∈ J, s(i, j) ∈ patternGem := by
  rcases hI with rfl | rfl | rfl <;>
    rcases hJ with rfl | rfl | rfl <;> decide +kernel

theorem gem_right_pairs_cross (I J : Finset (Fin 5))
    (hI : I = {4, 2} ∨ I = {4, 0} ∨ I = {0, 1})
    (hJ : J = {4, 2} ∨ J = {4, 0} ∨ J = {0, 1}) :
    ∃ i ∈ I, ∃ j ∈ J, s(i, j) ∈ patternGem := by
  rcases hI with rfl | rfl | rfl <;>
    rcases hJ with rfl | rfl | rfl <;> decide +kernel

end TaskH.Five

#print axioms TaskH.Five.star_extra_reindex
#print axioms TaskH.Five.gem_extra_reindex
#print axioms TaskH.Five.star_pairs_cross
#print axioms TaskH.Five.gem_left_pairs_cross
#print axioms TaskH.Five.gem_right_pairs_cross
