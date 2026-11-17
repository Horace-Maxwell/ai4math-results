import Research.TaskH.Seven.SevenBPSharedHookGroups

/-! Quad-hook to adjacent-hook capacity. Two explicitly finite Fin4 subset
supports are checked; arbitrary Fin16 sets are transported symbolically. -/

set_option autoImplicit false

namespace TaskH.Seven.BP

def quadAllowedOne (A C : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun t => t + 3 ∉ A ∧ t + 1 ∉ C)

def quadAllowedThree (A C : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun t => t + 2 ∉ A ∧ t + 3 ∉ C)

theorem quad_group_neighbor_capacity (A C : Finset (Fin 4))
    (ha : A.card = 2) (hc : C.card = 2)
    (hA : ∀ t : Fin 4, t ∈ A → t + 1 ∉ A)
    (hC : ∀ t : Fin 4, t ∈ C → t + 1 ∉ C) :
    (quadAllowedOne A C).card + (quadAllowedThree A C).card ≤ 2 := by
  have hh : ∀ A C : Finset (Fin 4), A.card = 2 → C.card = 2 →
      (∀ t : Fin 4, t ∈ A → t + 1 ∉ A) →
      (∀ t : Fin 4, t ∈ C → t + 1 ∉ C) →
      (quadAllowedOne A C).card + (quadAllowedThree A C).card ≤ 2 := by
    unfold quadAllowedOne quadAllowedThree
    decide +kernel
  exact hh A C ha hc hA hC

theorem quad_even_adjacent_odd_capacity (A B : Finset (Fin 16))
    (hA : ∀ i : Fin 16, i ∈ A → i + 4 ∉ A)
    (hpA : ∀ i : Fin 16, i ∈ A → i.val % 2 = 0)
    (hpB : ∀ i : Fin 16, i ∈ B → i.val % 2 = 1)
    (h5 : ∀ i : Fin 16, i ∈ A → i + 5 ∉ B)
    (h11 : ∀ i : Fin 16, i ∈ A → i + 11 ∉ B)
    (ha : A.card = 4) : B.card ≤ 2 := by
  classical
  have ac := chord_residue_card_partition A 0
  have bc := chord_residue_card_partition B 0
  have ae1 := residue_empty_of_parity A 0 hpA 1 (by decide)
  have ae3 := residue_empty_of_parity A 0 hpA 3 (by decide)
  have be0 := residue_empty_of_parity B 1 hpB 0 (by decide)
  have be2 := residue_empty_of_parity B 1 hpB 2 (by decide)
  rw [ae1, ae3, Finset.card_empty] at ac
  rw [be0, be2, Finset.card_empty] at bc
  have hA0 := no_four_step_residue_card A hA 0
  have hA2 := no_four_step_residue_card A hA 2
  have ha0 : (chordResidueGroup A 0 0).card = 2 := by omega
  have ha2 : (chordResidueGroup A 0 2).card = 2 := by omega
  have tab : ∀ t : Fin 4,
      chordGroupIndex 0 (t + 3) + 5 = chordGroupIndex 1 t ∧
      chordGroupIndex 2 (t + 1) + 11 = chordGroupIndex 1 t ∧
      chordGroupIndex 0 (t + 2) + 11 = chordGroupIndex 3 t ∧
      chordGroupIndex 2 (t + 3) + 5 = chordGroupIndex 3 t := by
    decide +kernel
  have hs1 : chordResidueGroup B 0 1 ⊆
      quadAllowedOne (chordResidueGroup A 0 0) (chordResidueGroup A 0 2) := by
    intro t ht
    have hb : chordGroupIndex 1 t ∈ B := by
      simpa only [zero_add] using (mem_chordResidueGroup B 0 1 t).mp ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro he
      have hh := h5 (chordGroupIndex 0 (t + 3)) (by
        simpa only [zero_add] using (mem_chordResidueGroup A 0 0 (t + 3)).mp he)
      exact hh ((tab t).1.symm ▸ hb)
    · intro he
      have hh := h11 (chordGroupIndex 2 (t + 1)) (by
        simpa only [zero_add] using (mem_chordResidueGroup A 0 2 (t + 1)).mp he)
      exact hh ((tab t).2.1.symm ▸ hb)
  have hs3 : chordResidueGroup B 0 3 ⊆
      quadAllowedThree (chordResidueGroup A 0 0) (chordResidueGroup A 0 2) := by
    intro t ht
    have hb : chordGroupIndex 3 t ∈ B := by
      simpa only [zero_add] using (mem_chordResidueGroup B 0 3 t).mp ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro he
      have hh := h11 (chordGroupIndex 0 (t + 2)) (by
        simpa only [zero_add] using (mem_chordResidueGroup A 0 0 (t + 2)).mp he)
      exact hh ((tab t).2.2.1.symm ▸ hb)
    · intro he
      have hh := h5 (chordGroupIndex 2 (t + 3)) (by
        simpa only [zero_add] using (mem_chordResidueGroup A 0 2 (t + 3)).mp he)
      exact hh ((tab t).2.2.2.symm ▸ hb)
  have h1 := Finset.card_le_card hs1
  have h3 := Finset.card_le_card hs3
  have hc := quad_group_neighbor_capacity _ _ ha0 ha2
    (residue_no_four_step A hA 0) (residue_no_four_step A hA 2)
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.quadAllowedOne
#print axioms TaskH.Seven.BP.quadAllowedThree
#print axioms TaskH.Seven.BP.quad_group_neighbor_capacity
#print axioms TaskH.Seven.BP.quad_even_adjacent_odd_capacity
