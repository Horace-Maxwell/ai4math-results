import Research.TaskH.Six.CycleSix

/-!
The twelve symmetries of a fixed six-position circle. All kernel computations
in this module concern only Bool and Fin 6, never an arbitrary graph.
-/

set_option autoImplicit false

namespace TaskH.Six

def HexagonIndexAdj (a b : Fin 6) : Prop := b = a + 1 ∨ b = a - 1

def hexagonOrientedIndex (reverse : Bool) (a i : Fin 6) : Fin 6 :=
  if reverse then a - i else a + i

theorem hexagon_index_edge_iff (a b : Fin 6) :
    s(a, b) ∈ hexagonEdges (id : Fin 6 → Fin 6) ↔ HexagonIndexAdj a b := by
  revert a b
  unfold HexagonIndexAdj
  decide +kernel

theorem hexagonOrientedIndex_zero (reverse : Bool) (a : Fin 6) :
    hexagonOrientedIndex reverse a 0 = a := by
  cases reverse <;> simp [hexagonOrientedIndex]

theorem hexagonOrientedIndex_injective (reverse : Bool) (a : Fin 6) :
    Function.Injective (hexagonOrientedIndex reverse a) := by
  revert reverse a
  decide +kernel

theorem hexagonOrientedIndex_adj (reverse : Bool) (a i : Fin 6) :
    HexagonIndexAdj (hexagonOrientedIndex reverse a i)
      (hexagonOrientedIndex reverse a (i + 1)) := by
  revert reverse a i
  unfold HexagonIndexAdj
  decide +kernel

theorem hexagonOrientedIndex_edges (reverse : Bool) (a : Fin 6) :
    hexagonEdges (hexagonOrientedIndex reverse a) =
      hexagonEdges (id : Fin 6 → Fin 6) := by
  revert reverse a
  decide +kernel

theorem hexagonOrientedIndex_parameters_injective :
    Function.Injective (fun o : Bool × Fin 6 => hexagonOrientedIndex o.1 o.2) := by
  decide +kernel

theorem hexagonOrientedIndex_next_unique (reverse : Bool) (a i c : Fin 6)
    (hc : HexagonIndexAdj (hexagonOrientedIndex reverse a i) c)
    (hne : c ≠ hexagonOrientedIndex reverse a (i - 1)) :
    c = hexagonOrientedIndex reverse a (i + 1) := by
  revert reverse a i c
  unfold HexagonIndexAdj
  decide +kernel

theorem hexagon_index_word_eq_of_first_two
    (σ : Fin 6 → Fin 6) (hσ : Function.Injective σ)
    (hstep : ∀ i, HexagonIndexAdj (σ i) (σ (i + 1)))
    (reverse : Bool) (a : Fin 6)
    (h0 : σ 0 = hexagonOrientedIndex reverse a 0)
    (h1 : σ 1 = hexagonOrientedIndex reverse a 1) :
    σ = hexagonOrientedIndex reverse a := by
  have h2 : σ 2 = hexagonOrientedIndex reverse a 2 := by
    apply hexagonOrientedIndex_next_unique reverse a 1 (σ 2)
    · rw [← h1]
      exact hstep 1
    · rw [show (1 : Fin 6) - 1 = 0 by decide, ← h0]
      exact hσ.ne (by decide)
  have h3 : σ 3 = hexagonOrientedIndex reverse a 3 := by
    apply hexagonOrientedIndex_next_unique reverse a 2 (σ 3)
    · rw [← h2]
      exact hstep 2
    · rw [show (2 : Fin 6) - 1 = 1 by decide, ← h1]
      exact hσ.ne (by decide)
  have h4 : σ 4 = hexagonOrientedIndex reverse a 4 := by
    apply hexagonOrientedIndex_next_unique reverse a 3 (σ 4)
    · rw [← h3]
      exact hstep 3
    · rw [show (3 : Fin 6) - 1 = 2 by decide, ← h2]
      exact hσ.ne (by decide)
  have h5 : σ 5 = hexagonOrientedIndex reverse a 5 := by
    apply hexagonOrientedIndex_next_unique reverse a 4 (σ 5)
    · rw [← h4]
      exact hstep 4
    · rw [show (4 : Fin 6) - 1 = 3 by decide, ← h3]
      exact hσ.ne (by decide)
  funext i
  fin_cases i <;> assumption

theorem hexagon_index_word_dihedral
    (σ : Fin 6 → Fin 6) (hσ : Function.Injective σ)
    (hstep : ∀ i, HexagonIndexAdj (σ i) (σ (i + 1))) :
    ∃ o : Bool × Fin 6, σ = hexagonOrientedIndex o.1 o.2 := by
  rcases hstep 0 with hp | hm
  · refine ⟨(false, σ 0), ?_⟩
    apply hexagon_index_word_eq_of_first_two σ hσ hstep false (σ 0)
    · simp [hexagonOrientedIndex]
    · simpa [hexagonOrientedIndex] using hp
  · refine ⟨(true, σ 0), ?_⟩
    apply hexagon_index_word_eq_of_first_two σ hσ hstep true (σ 0)
    · simp [hexagonOrientedIndex]
    · simpa [hexagonOrientedIndex] using hm

end TaskH.Six

#print axioms TaskH.Six.HexagonIndexAdj
#print axioms TaskH.Six.hexagonOrientedIndex
#print axioms TaskH.Six.hexagon_index_edge_iff
#print axioms TaskH.Six.hexagonOrientedIndex_zero
#print axioms TaskH.Six.hexagonOrientedIndex_injective
#print axioms TaskH.Six.hexagonOrientedIndex_adj
#print axioms TaskH.Six.hexagonOrientedIndex_edges
#print axioms TaskH.Six.hexagonOrientedIndex_parameters_injective
#print axioms TaskH.Six.hexagonOrientedIndex_next_unique
#print axioms TaskH.Six.hexagon_index_word_eq_of_first_two
#print axioms TaskH.Six.hexagon_index_word_dihedral
