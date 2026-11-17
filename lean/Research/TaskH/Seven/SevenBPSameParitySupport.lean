import Research.TaskH.Seven.SevenBPChordResidues

/-! Same-parity C16 attachment indices: use four residue groups and their
four-position no-adjacent bound. No Fin16 subset configurations are enumerated. -/

set_option autoImplicit false

namespace TaskH.Seven.BP

theorem chordGroupIndex_mod_two (r t : Fin 4) :
    (chordGroupIndex r t).val % 2 = r.val % 2 := by
  revert r t
  decide +kernel

theorem no_four_step_residue_card (S : Finset (Fin 16))
    (hs : ∀ i : Fin 16, i ∈ S → i + 4 ∉ S) (r : Fin 4) :
    (chordResidueGroup S 0 r).card ≤ 2 := by
  apply four_groups_no_adjacent_card
  intro t ht hnext
  have hi : chordGroupIndex r t ∈ S := by
    simpa only [zero_add] using (mem_chordResidueGroup S 0 r t).mp ht
  have hj : chordGroupIndex r t + 4 ∈ S := by
    simpa only [zero_add, chordGroupIndex_add_four] using
      (mem_chordResidueGroup S 0 r (t + 1)).mp hnext
  exact hs _ hi hj

theorem residue_empty_of_parity (S : Finset (Fin 16)) (b : ℕ)
    (hp : ∀ i : Fin 16, i ∈ S → i.val % 2 = b) (r : Fin 4)
    (hr : r.val % 2 ≠ b) : chordResidueGroup S 0 r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hi : chordGroupIndex r t ∈ S := by
    simpa only [zero_add] using (mem_chordResidueGroup S 0 r t).mp ht
  exact hr ((chordGroupIndex_mod_two r t).symm.trans (hp _ hi))

theorem same_parity_no_four_step_card_le_four (S : Finset (Fin 16))
    (hs : ∀ i : Fin 16, i ∈ S → i + 4 ∉ S)
    (hp : ∀ i : Fin 16, i ∈ S → ∀ j : Fin 16, j ∈ S → i.val % 2 = j.val % 2) :
    S.card ≤ 4 := by
  classical
  by_cases he : S = ∅
  · rw [he]
    exact Nat.zero_le _
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hpar : ∀ j : Fin 16, j ∈ S → j.val % 2 = i.val % 2 :=
    fun j hj => hp j hj i hi
  have h0 := no_four_step_residue_card S hs 0
  have h1 := no_four_step_residue_card S hs 1
  have h2 := no_four_step_residue_card S hs 2
  have h3 := no_four_step_residue_card S hs 3
  have hc := chord_residue_card_partition S 0
  by_cases hb : i.val % 2 = 0
  · have he1 : chordResidueGroup S 0 1 = ∅ :=
      residue_empty_of_parity S _ hpar 1 (by change 1 % 2 ≠ i.val % 2; omega)
    have he3 : chordResidueGroup S 0 3 = ∅ :=
      residue_empty_of_parity S _ hpar 3 (by change 3 % 2 ≠ i.val % 2; omega)
    rw [he1, he3] at hc
    simp only [Finset.card_empty] at hc
    omega
  · have hb1 : i.val % 2 = 1 := by omega
    have he0 : chordResidueGroup S 0 0 = ∅ :=
      residue_empty_of_parity S _ hpar 0 (by change 0 % 2 ≠ i.val % 2; omega)
    have he2 : chordResidueGroup S 0 2 = ∅ :=
      residue_empty_of_parity S _ hpar 2 (by change 2 % 2 ≠ i.val % 2; omega)
    rw [he0, he2] at hc
    simp only [Finset.card_empty] at hc
    omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.chordGroupIndex_mod_two
#print axioms TaskH.Seven.BP.no_four_step_residue_card
#print axioms TaskH.Seven.BP.residue_empty_of_parity
#print axioms TaskH.Seven.BP.same_parity_no_four_step_card_le_four
