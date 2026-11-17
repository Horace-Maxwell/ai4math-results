import Research.TaskH.Seven.SevenBPChordGroups

/-! Actual modulo-four groups of arbitrary Fin16 index sets. No graph or
index-set configuration is enumerated; only the displayed Fin4 index identities
are checked by the kernel. -/

set_option autoImplicit false

namespace TaskH.Seven.BP

open scoped BigOperators

def chordGroupIndex (r t : Fin 4) : Fin 16 := finProdFinEquiv (t, r)

def chordResidueGroup (E : Finset (Fin 16)) (o : Fin 16) (r : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun t => o + chordGroupIndex r t ∈ E)

theorem mem_chordResidueGroup (E : Finset (Fin 16)) (o : Fin 16) (r t : Fin 4) :
    t ∈ chordResidueGroup E o r ↔ o + chordGroupIndex r t ∈ E := by
  simp only [chordResidueGroup, Finset.mem_filter, Finset.mem_univ, true_and]

theorem chordGroupIndex_add_four (r t : Fin 4) :
    chordGroupIndex r t + 4 = chordGroupIndex r (t + 1) := by
  revert r t
  decide +kernel

theorem chord_residue_card_partition (E : Finset (Fin 16)) (o : Fin 16) :
    E.card = (chordResidueGroup E o 0).card + (chordResidueGroup E o 1).card +
      (chordResidueGroup E o 2).card + (chordResidueGroup E o 3).card := by
  classical
  let P : Finset (Fin 4 × Fin 4) :=
    Finset.univ.filter (fun p => o + finProdFinEquiv p ∈ E)
  have hcard : P.card = E.card := by
    apply Finset.card_bij (fun p _ => o + finProdFinEquiv p)
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p _ q _ he
      exact finProdFinEquiv.injective (add_left_cancel he)
    · intro x hx
      refine ⟨finProdFinEquiv.symm (x - o), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by
          simpa only [Equiv.apply_symm_apply, add_comm o (x - o), sub_add_cancel] using hx⟩
      · simp only [Equiv.apply_symm_apply, add_comm o (x - o), sub_add_cancel]
  have hsum : P.card = ∑ r : Fin 4, (chordResidueGroup E o r).card := by
    simp only [P, chordResidueGroup, Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hcard] at hsum
  simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum

theorem chord_residue_five_restrictions (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) (o : Fin 16) :
    FiveGroupRestrictions (chordResidueGroup E o 0) (chordResidueGroup E o 1)
      (chordResidueGroup E o 2) (chordResidueGroup E o 3) := by
  have hstep (r t : Fin 4) (hr : r = 0 ∨ r = 1) :
      chordGroupIndex r t + 2 = chordGroupIndex (r + 2) t ∧
      chordGroupIndex (r + 2) (t + 3) + 2 = chordGroupIndex r t := by
    have ht : ∀ r t : Fin 4, r = 0 ∨ r = 1 →
        chordGroupIndex r t + 2 = chordGroupIndex (r + 2) t ∧
        chordGroupIndex (r + 2) (t + 3) + 2 = chordGroupIndex r t := by decide +kernel
    exact ht r t hr
  have hsep (r : Fin 4) (hr : r = 0 ∨ r = 1) :
      GroupSeparated (chordResidueGroup E o r) (chordResidueGroup E o (r + 2)) := by
    intro t ht
    have he := (mem_chordResidueGroup E o r t).mp ht
    constructor
    · intro hc
      have hh := h.1 (o + chordGroupIndex r t) he
      apply hh
      simpa only [add_assoc, (hstep r t hr).1] using
        (mem_chordResidueGroup E o (r + 2) t).mp hc
    · intro hc
      have hh := h.1 (o + chordGroupIndex (r + 2) (t + 3))
        ((mem_chordResidueGroup E o (r + 2) (t + 3)).mp hc)
      apply hh
      simpa only [add_assoc, (hstep r t hr).2] using he
  have hAC : GroupSeparated (chordResidueGroup E o 0) (chordResidueGroup E o 2) := by
    simpa only [show (0 : Fin 4) + 2 = 2 by decide] using hsep 0 (Or.inl rfl)
  have hBD : GroupSeparated (chordResidueGroup E o 1) (chordResidueGroup E o 3) := by
    simpa only [show (1 : Fin 4) + 2 = 3 by decide] using hsep 1 (Or.inr rfl)
  refine ⟨hAC, hBD, ?_, ?_, ?_, ?_⟩
  · intro t ht hu hv
    have hnext : chordGroupIndex 0 t + 1 = chordGroupIndex 1 t := by
      have hh : ∀ t : Fin 4, chordGroupIndex 0 t + 1 =
          chordGroupIndex 1 t := by decide +kernel
      exact hh t
    have he := (mem_chordResidueGroup E o 0 t).mp ht
    have hn : o + chordGroupIndex 0 t + 1 ∈ E := by
      simpa only [add_assoc, hnext] using
        (mem_chordResidueGroup E o 1 t).mp hu
    have hh := h.2.1 (o + chordGroupIndex 0 t) he hn
    apply hh
    simpa only [add_assoc, chordGroupIndex_add_four] using
      (mem_chordResidueGroup E o 0 (t + 1)).mp hv
  · intro t ht hu hv
    have hnext : chordGroupIndex 1 t + 1 = chordGroupIndex 2 t := by
      have hh : ∀ t : Fin 4, chordGroupIndex 1 t + 1 =
          chordGroupIndex 2 t := by decide +kernel
      exact hh t
    have he := (mem_chordResidueGroup E o 1 t).mp ht
    have hn : o + chordGroupIndex 1 t + 1 ∈ E := by
      simpa only [add_assoc, hnext] using
        (mem_chordResidueGroup E o 2 t).mp hu
    have hh := h.2.1 (o + chordGroupIndex 1 t) he hn
    apply hh
    simpa only [add_assoc, chordGroupIndex_add_four] using
      (mem_chordResidueGroup E o 1 (t + 1)).mp hv
  · intro t ht hu hv
    have hnext : chordGroupIndex 2 t + 1 = chordGroupIndex 3 t := by
      have hh : ∀ t : Fin 4, chordGroupIndex 2 t + 1 =
          chordGroupIndex 3 t := by decide +kernel
      exact hh t
    have he := (mem_chordResidueGroup E o 2 t).mp ht
    have hn : o + chordGroupIndex 2 t + 1 ∈ E := by
      simpa only [add_assoc, hnext] using
        (mem_chordResidueGroup E o 3 t).mp hu
    have hh := h.2.1 (o + chordGroupIndex 2 t) he hn
    apply hh
    simpa only [add_assoc, chordGroupIndex_add_four] using
      (mem_chordResidueGroup E o 2 (t + 1)).mp hv
  · intro t ht hu hv
    have hnext : chordGroupIndex 3 t + 1 = chordGroupIndex 0 (t + 1) := by
      have hh : ∀ t : Fin 4, chordGroupIndex 3 t + 1 =
          chordGroupIndex 0 (t + 1) := by decide +kernel
      exact hh t
    have he := (mem_chordResidueGroup E o 3 t).mp ht
    have hn : o + chordGroupIndex 3 t + 1 ∈ E := by
      simpa only [add_assoc, hnext] using
        (mem_chordResidueGroup E o 0 (t + 1)).mp hu
    have hh := h.2.1 (o + chordGroupIndex 3 t) he hn
    apply hh
    simpa only [add_assoc, chordGroupIndex_add_four] using
      (mem_chordResidueGroup E o 3 (t + 1)).mp hv

theorem fiveChordIndices_card_le_six_of_restrictions (E F : Finset (Fin 16))
    (h : ChordRestrictions E F) : E.card ≤ 6 := by
  have he := five_groups_card_le_six _ _ _ _ (chord_residue_five_restrictions E F h 0)
  rw [chord_residue_card_partition E 0]
  exact he

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.chordGroupIndex
#print axioms TaskH.Seven.BP.chordResidueGroup
#print axioms TaskH.Seven.BP.mem_chordResidueGroup
#print axioms TaskH.Seven.BP.chordGroupIndex_add_four
#print axioms TaskH.Seven.BP.chord_residue_card_partition
#print axioms TaskH.Seven.BP.chord_residue_five_restrictions
#print axioms TaskH.Seven.BP.fiveChordIndices_card_le_six_of_restrictions
