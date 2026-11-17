import Research.TaskH.Seven.CycleSeven

/-!
The fourteen symmetries of a fixed seven-position circle. All kernel computations
in this module concern only Bool and Fin 7, never an arbitrary graph.
-/

set_option autoImplicit false

namespace TaskH.Seven

def HeptagonIndexAdj (a b : Fin 7) : Prop := b = a + 1 ∨ b = a - 1

def heptagonOrientedIndex (reverse : Bool) (a i : Fin 7) : Fin 7 :=
  if reverse then a - i else a + i

theorem heptagon_index_edge_iff (a b : Fin 7) :
    s(a, b) ∈ heptagonEdges (id : Fin 7 → Fin 7) ↔ HeptagonIndexAdj a b := by
  revert a b
  unfold HeptagonIndexAdj
  decide +kernel

theorem heptagonOrientedIndex_zero (reverse : Bool) (a : Fin 7) :
    heptagonOrientedIndex reverse a 0 = a := by
  cases reverse <;> simp [heptagonOrientedIndex]

theorem heptagonOrientedIndex_injective (reverse : Bool) (a : Fin 7) :
    Function.Injective (heptagonOrientedIndex reverse a) := by
  revert reverse a
  decide +kernel

theorem heptagonOrientedIndex_adj (reverse : Bool) (a i : Fin 7) :
    HeptagonIndexAdj (heptagonOrientedIndex reverse a i)
      (heptagonOrientedIndex reverse a (i + 1)) := by
  revert reverse a i
  unfold HeptagonIndexAdj
  decide +kernel

theorem heptagonOrientedIndex_edges (reverse : Bool) (a : Fin 7) :
    heptagonEdges (heptagonOrientedIndex reverse a) =
      heptagonEdges (id : Fin 7 → Fin 7) := by
  revert reverse a
  decide +kernel

theorem heptagonOrientedIndex_parameters_injective :
    Function.Injective (fun o : Bool × Fin 7 => heptagonOrientedIndex o.1 o.2) := by
  decide +kernel

theorem heptagonOrientedIndex_next_unique (reverse : Bool) (a i c : Fin 7)
    (hc : HeptagonIndexAdj (heptagonOrientedIndex reverse a i) c)
    (hne : c ≠ heptagonOrientedIndex reverse a (i - 1)) :
    c = heptagonOrientedIndex reverse a (i + 1) := by
  revert reverse a i c
  unfold HeptagonIndexAdj
  decide +kernel

theorem heptagon_index_word_eq_of_first_two
    (σ : Fin 7 → Fin 7) (hσ : Function.Injective σ)
    (hstep : ∀ i, HeptagonIndexAdj (σ i) (σ (i + 1)))
    (reverse : Bool) (a : Fin 7)
    (h0 : σ 0 = heptagonOrientedIndex reverse a 0)
    (h1 : σ 1 = heptagonOrientedIndex reverse a 1) :
    σ = heptagonOrientedIndex reverse a := by
  have h2 : σ 2 = heptagonOrientedIndex reverse a 2 := by
    apply heptagonOrientedIndex_next_unique reverse a 1 (σ 2)
    · rw [← h1]
      exact hstep 1
    · rw [show (1 : Fin 7) - 1 = 0 by decide, ← h0]
      exact hσ.ne (by decide)
  have h3 : σ 3 = heptagonOrientedIndex reverse a 3 := by
    apply heptagonOrientedIndex_next_unique reverse a 2 (σ 3)
    · rw [← h2]
      exact hstep 2
    · rw [show (2 : Fin 7) - 1 = 1 by decide, ← h1]
      exact hσ.ne (by decide)
  have h4 : σ 4 = heptagonOrientedIndex reverse a 4 := by
    apply heptagonOrientedIndex_next_unique reverse a 3 (σ 4)
    · rw [← h3]
      exact hstep 3
    · rw [show (3 : Fin 7) - 1 = 2 by decide, ← h2]
      exact hσ.ne (by decide)
  have h5 : σ 5 = heptagonOrientedIndex reverse a 5 := by
    apply heptagonOrientedIndex_next_unique reverse a 4 (σ 5)
    · rw [← h4]
      exact hstep 4
    · rw [show (4 : Fin 7) - 1 = 3 by decide, ← h3]
      exact hσ.ne (by decide)
  have h6 : σ 6 = heptagonOrientedIndex reverse a 6 := by
    apply heptagonOrientedIndex_next_unique reverse a 5 (σ 6)
    · rw [← h5]
      exact hstep 5
    · rw [show (5 : Fin 7) - 1 = 4 by decide, ← h4]
      exact hσ.ne (by decide)
  funext i
  fin_cases i <;> assumption

theorem heptagon_index_word_dihedral
    (σ : Fin 7 → Fin 7) (hσ : Function.Injective σ)
    (hstep : ∀ i, HeptagonIndexAdj (σ i) (σ (i + 1))) :
    ∃ o : Bool × Fin 7, σ = heptagonOrientedIndex o.1 o.2 := by
  rcases hstep 0 with hp | hm
  · refine ⟨(false, σ 0), ?_⟩
    apply heptagon_index_word_eq_of_first_two σ hσ hstep false (σ 0)
    · simp [heptagonOrientedIndex]
    · simpa [heptagonOrientedIndex] using hp
  · refine ⟨(true, σ 0), ?_⟩
    apply heptagon_index_word_eq_of_first_two σ hσ hstep true (σ 0)
    · simp [heptagonOrientedIndex]
    · simpa [heptagonOrientedIndex] using hm

end TaskH.Seven

#print axioms TaskH.Seven.HeptagonIndexAdj
#print axioms TaskH.Seven.heptagonOrientedIndex
#print axioms TaskH.Seven.heptagon_index_edge_iff
#print axioms TaskH.Seven.heptagonOrientedIndex_zero
#print axioms TaskH.Seven.heptagonOrientedIndex_injective
#print axioms TaskH.Seven.heptagonOrientedIndex_adj
#print axioms TaskH.Seven.heptagonOrientedIndex_edges
#print axioms TaskH.Seven.heptagonOrientedIndex_parameters_injective
#print axioms TaskH.Seven.heptagonOrientedIndex_next_unique
#print axioms TaskH.Seven.heptagon_index_word_eq_of_first_two
#print axioms TaskH.Seven.heptagon_index_word_dihedral
