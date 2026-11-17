import Research.TaskH.Seven.SevenBPChordNormalize

/-! All mixed restrictions are transported from actual Fin16 index sets to
the four-position group budget; no group-coverage hypothesis is introduced. -/

set_option autoImplicit false

namespace TaskH.Seven.BP

theorem mixed_zero_group_subset (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) (o : Fin 16) :
    chordResidueGroup E o 0 ⊆ allowedZero (chordResidueGroup F o 1) := by
  intro t ht
  have he := (mem_chordResidueGroup E o 0 t).mp ht
  have hm := h.2.2.2.1 (o + chordGroupIndex 0 t) he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro hf
    have hi : chordGroupIndex 0 t + 1 = chordGroupIndex 1 t := by
      have tab : ∀ t : Fin 4, chordGroupIndex 0 t + 1 = chordGroupIndex 1 t := by decide +kernel
      exact tab t
    exact hm.1 (by simpa only [add_assoc, hi] using
      (mem_chordResidueGroup F o 1 t).mp hf)
  · intro hf
    have hi : chordGroupIndex 0 t + 13 = chordGroupIndex 1 (t + 3) := by
      have tab : ∀ t : Fin 4, chordGroupIndex 0 t + 13 = chordGroupIndex 1 (t + 3) := by decide +kernel
      exact tab t
    exact hm.2 (by simpa only [add_assoc, hi] using
      (mem_chordResidueGroup F o 1 (t + 3)).mp hf)

theorem mixed_three_group_subset (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) (o : Fin 16) :
    chordResidueGroup E o 3 ⊆ allowedThree (chordResidueGroup F o 0) := by
  intro t ht
  have he := (mem_chordResidueGroup E o 3 t).mp ht
  have hm := h.2.2.2.1 (o + chordGroupIndex 3 t) he
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro hf
    have hi : chordGroupIndex 3 t + 13 = chordGroupIndex 0 t := by
      have tab : ∀ t : Fin 4, chordGroupIndex 3 t + 13 = chordGroupIndex 0 t := by decide +kernel
      exact tab t
    exact hm.2 (by simpa only [add_assoc, hi] using
      (mem_chordResidueGroup F o 0 t).mp hf)
  · intro hf
    have hi : chordGroupIndex 3 t + 1 = chordGroupIndex 0 (t + 1) := by
      have tab : ∀ t : Fin 4, chordGroupIndex 3 t + 1 = chordGroupIndex 0 (t + 1) := by decide +kernel
      exact tab t
    exact hm.1 (by simpa only [add_assoc, hi] using
      (mem_chordResidueGroup F o 0 (t + 1)).mp hf)

theorem mixed_middle_group_subset (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) (o : Fin 16) (r : Fin 4) (hr : r = 1 ∨ r = 2) :
    chordResidueGroup E o r ⊆
      allowedMiddle (chordResidueGroup F o 0) (chordResidueGroup F o 1) := by
  intro t ht
  have he := (mem_chordResidueGroup E o r t).mp ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro k hk
  by_contra hpar
  have hk0 := (mem_chordResidueGroup F o 0 k).mp (Finset.mem_inter.mp hk).1
  have hk1 := (mem_chordResidueGroup F o 1 k).mp (Finset.mem_inter.mp hk).2
  have hi : chordGroupIndex 0 k + 1 = chordGroupIndex 1 k := by
    have tab : ∀ k : Fin 4, chordGroupIndex 0 k + 1 = chordGroupIndex 1 k := by decide +kernel
    exact tab k
  have hk1' : o + chordGroupIndex 0 k + 1 ∈ F := by
    simpa only [add_assoc, hi] using hk1
  have hm := h.2.2.2.2 (o + chordGroupIndex 0 k) hk0 hk1'
  have tab : ∀ r t k : Fin 4, r = 1 ∨ r = 2 → t.val % 2 ≠ k.val % 2 →
      chordGroupIndex r t = chordGroupIndex 0 k + 5 ∨
      chordGroupIndex r t = chordGroupIndex 0 k + 6 ∨
      chordGroupIndex r t = chordGroupIndex 0 k + 13 ∨
      chordGroupIndex r t = chordGroupIndex 0 k + 14 := by decide +kernel
  rcases tab r t k hr hpar with heq | heq | heq | heq
  · exact hm.1 (by simpa only [add_assoc, ← heq] using he)
  · exact hm.2.1 (by simpa only [add_assoc, ← heq] using he)
  · exact hm.2.2.1 (by simpa only [add_assoc, ← heq] using he)
  · exact hm.2.2.2 (by simpa only [add_assoc, ← heq] using he)

theorem chordRestrictions_card_le_eleven (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) : E.card + F.card ≤ 11 := by
  obtain ⟨o, h2, h3⟩ := seven_chord_normalized_origin E F h
  have hb := normalized_chord_total_le_eleven
    (chordResidueGroup E o 0) (chordResidueGroup E o 1)
    (chordResidueGroup E o 2) (chordResidueGroup E o 3)
    (chordResidueGroup F o 0) (chordResidueGroup F o 1)
    (chord_residue_five_restrictions E F h o)
    (mixed_zero_group_subset E F h o) (mixed_three_group_subset E F h o)
    (mixed_middle_group_subset E F h o 1 (Or.inl rfl))
    (mixed_middle_group_subset E F h o 2 (Or.inr rfl))
  rw [chord_residue_card_partition E o, normalized_seven_chord_card F o h2 h3]
  omega

universe u
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

theorem actual_five_seven_chord_card_le_eleven (u : Fin 16 → V)
    (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G) :
    (fiveChordIndices G u).card + (sevenChordIndices G u).card ≤ 11 :=
  chordRestrictions_card_le_eleven _ _ (actual_chord_restrictions u hu hn)

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.mixed_zero_group_subset
#print axioms TaskH.Seven.BP.mixed_three_group_subset
#print axioms TaskH.Seven.BP.mixed_middle_group_subset
#print axioms TaskH.Seven.BP.chordRestrictions_card_le_eleven
#print axioms TaskH.Seven.BP.actual_five_seven_chord_card_le_eleven
