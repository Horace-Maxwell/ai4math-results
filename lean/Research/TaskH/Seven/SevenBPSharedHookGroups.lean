import Research.TaskH.Seven.SevenBPSameParitySupport

/-! Shared-neighbor hook capacities in four-position residue groups.
The finite subset checks are explicitly on Fin4 only, not graphs, Fin16
subsets, vertex permutations or arbitrary chord configurations. -/

set_option autoImplicit false

namespace TaskH.Seven.BP

def EarSeparated (A B : Finset (Fin 4)) : Prop :=
  ∀ t : Fin 4, t ∈ A → t + 1 ∉ B ∧ t + 2 ∉ B

def EarSeparatedBack (A B : Finset (Fin 4)) : Prop :=
  ∀ t : Fin 4, t ∈ A → t + 2 ∉ B ∧ t + 3 ∉ B

theorem earSeparated_two_forces_empty (A B : Finset (Fin 4))
    (ha : A.card = 2) (hn : ∀ t : Fin 4, t ∈ A → t + 1 ∉ A)
    (he : EarSeparated A B) : B = ∅ := by
  have hh : ∀ A B : Finset (Fin 4), A.card = 2 →
      (∀ t : Fin 4, t ∈ A → t + 1 ∉ A) → EarSeparated A B → B = ∅ := by
    unfold EarSeparated
    decide +kernel
  exact hh A B ha hn he

theorem earSeparated_nonempty_card (A B : Finset (Fin 4))
    (ha : A.Nonempty) (hn : ∀ t : Fin 4, t ∈ B → t + 1 ∉ B)
    (he : EarSeparated A B) : B.card ≤ 1 := by
  have hh : ∀ A B : Finset (Fin 4), A.Nonempty →
      (∀ t : Fin 4, t ∈ B → t + 1 ∉ B) → EarSeparated A B → B.card ≤ 1 := by
    unfold EarSeparated
    decide +kernel
  exact hh A B ha hn he

theorem earSeparatedBack_two_forces_empty (A B : Finset (Fin 4))
    (ha : A.card = 2) (hn : ∀ t : Fin 4, t ∈ A → t + 1 ∉ A)
    (he : EarSeparatedBack A B) : B = ∅ := by
  have hh : ∀ A B : Finset (Fin 4), A.card = 2 →
      (∀ t : Fin 4, t ∈ A → t + 1 ∉ A) → EarSeparatedBack A B → B = ∅ := by
    unfold EarSeparatedBack
    decide +kernel
  exact hh A B ha hn he

theorem earSeparatedBack_nonempty_card (A B : Finset (Fin 4))
    (ha : A.Nonempty) (hn : ∀ t : Fin 4, t ∈ B → t + 1 ∉ B)
    (he : EarSeparatedBack A B) : B.card ≤ 1 := by
  have hh : ∀ A B : Finset (Fin 4), A.Nonempty →
      (∀ t : Fin 4, t ∈ B → t + 1 ∉ B) → EarSeparatedBack A B → B.card ≤ 1 := by
    unfold EarSeparatedBack
    decide +kernel
  exact hh A B ha hn he

theorem four_group_high_shared_capacity (A C B D : Finset (Fin 4))
    (hA : ∀ t : Fin 4, t ∈ A → t + 1 ∉ A)
    (hC : ∀ t : Fin 4, t ∈ C → t + 1 ∉ C)
    (hB : ∀ t : Fin 4, t ∈ B → t + 1 ∉ B)
    (hD : ∀ t : Fin 4, t ∈ D → t + 1 ∉ D)
    (hAD : EarSeparated A D) (hCB : EarSeparatedBack C B)
    (ha : 3 ≤ A.card + C.card) : B.card + D.card ≤ 1 := by
  have ha2 := four_groups_no_adjacent_card A hA
  have hc2 := four_groups_no_adjacent_card C hC
  by_cases h : A.card = 2
  · have hd := earSeparated_two_forces_empty A D h hA hAD
    have hc : C.Nonempty := Finset.card_pos.mp (by omega)
    have hb := earSeparatedBack_nonempty_card C B hc hB hCB
    rw [hd, Finset.card_empty]
    omega
  · have hc : C.card = 2 := by omega
    have hb := earSeparatedBack_two_forces_empty C B hc hC hCB
    have han : A.Nonempty := Finset.card_pos.mp (by omega)
    have hd := earSeparated_nonempty_card A D han hD hAD
    rw [hb, Finset.card_empty]
    omega

theorem four_group_quad_shared_empty (A C B D : Finset (Fin 4))
    (hA : ∀ t : Fin 4, t ∈ A → t + 1 ∉ A)
    (hC : ∀ t : Fin 4, t ∈ C → t + 1 ∉ C)
    (hAD : EarSeparated A D) (hCB : EarSeparatedBack C B)
    (ha : 4 ≤ A.card + C.card) : B.card + D.card = 0 := by
  have ha2 := four_groups_no_adjacent_card A hA
  have hc2 := four_groups_no_adjacent_card C hC
  have heA : A.card = 2 := by omega
  have heC : C.card = 2 := by omega
  rw [earSeparated_two_forces_empty A D heA hA hAD,
    earSeparatedBack_two_forces_empty C B heC hC hCB, Finset.card_empty]

theorem residue_no_four_step (S : Finset (Fin 16))
    (hs : ∀ i : Fin 16, i ∈ S → i + 4 ∉ S) (r : Fin 4) :
    ∀ t : Fin 4, t ∈ chordResidueGroup S 0 r →
      t + 1 ∉ chordResidueGroup S 0 r := by
  intro t ht hu
  have hi : chordGroupIndex r t ∈ S := by
    simpa only [zero_add] using (mem_chordResidueGroup S 0 r t).mp ht
  have hj : chordGroupIndex r t + 4 ∈ S := by
    simpa only [zero_add, chordGroupIndex_add_four] using
      (mem_chordResidueGroup S 0 r (t + 1)).mp hu
  exact hs _ hi hj

theorem shared_residue_separated (A B : Finset (Fin 16))
    (h6 : ∀ i : Fin 16, i ∈ A → i + 6 ∉ B)
    (h10 : ∀ i : Fin 16, i ∈ A → i + 10 ∉ B)
    (r : Fin 4) (hr : r = 0 ∨ r = 1) :
    EarSeparated (chordResidueGroup A 0 r) (chordResidueGroup B 0 (r + 2)) ∧
    EarSeparatedBack (chordResidueGroup A 0 (r + 2)) (chordResidueGroup B 0 r) := by
  have ht : ∀ r t : Fin 4, r = 0 ∨ r = 1 →
      chordGroupIndex r t + 6 = chordGroupIndex (r + 2) (t + 1) ∧
      chordGroupIndex r t + 10 = chordGroupIndex (r + 2) (t + 2) ∧
      chordGroupIndex (r + 2) t + 6 = chordGroupIndex r (t + 2) ∧
      chordGroupIndex (r + 2) t + 10 = chordGroupIndex r (t + 3) := by
    decide +kernel
  constructor
  · intro t ha
    have hi : chordGroupIndex r t ∈ A := by
      simpa only [zero_add] using (mem_chordResidueGroup A 0 r t).mp ha
    constructor
    · intro hb
      apply h6 _ hi
      simpa only [(ht r t hr).1, zero_add] using
        (mem_chordResidueGroup B 0 (r + 2) (t + 1)).mp hb
    · intro hb
      apply h10 _ hi
      simpa only [(ht r t hr).2.1, zero_add] using
        (mem_chordResidueGroup B 0 (r + 2) (t + 2)).mp hb
  · intro t ha
    have hi : chordGroupIndex (r + 2) t ∈ A := by
      simpa only [zero_add] using (mem_chordResidueGroup A 0 (r + 2) t).mp ha
    constructor
    · intro hb
      apply h6 _ hi
      simpa only [(ht r t hr).2.2.1, zero_add] using
        (mem_chordResidueGroup B 0 r (t + 2)).mp hb
    · intro hb
      apply h10 _ hi
      simpa only [(ht r t hr).2.2.2, zero_add] using
        (mem_chordResidueGroup B 0 r (t + 3)).mp hb

theorem same_parity_shared_high_capacity (A B : Finset (Fin 16)) (b : ℕ)
    (hA : ∀ i : Fin 16, i ∈ A → i + 4 ∉ A)
    (hB : ∀ i : Fin 16, i ∈ B → i + 4 ∉ B)
    (hpA : ∀ i : Fin 16, i ∈ A → i.val % 2 = b)
    (hpB : ∀ i : Fin 16, i ∈ B → i.val % 2 = b)
    (h6 : ∀ i : Fin 16, i ∈ A → i + 6 ∉ B)
    (h10 : ∀ i : Fin 16, i ∈ A → i + 10 ∉ B)
    (ha : 3 ≤ A.card) : B.card ≤ 1 ∧ (4 ≤ A.card → B.card = 0) := by
  classical
  have ac := chord_residue_card_partition A 0
  have bc := chord_residue_card_partition B 0
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hb : b = 0 ∨ b = 1 := by have h := hpA i hi; omega
  have core (r : Fin 4) (hr : r = 0 ∨ r = 1)
      (ha : 3 ≤ (chordResidueGroup A 0 r).card +
        (chordResidueGroup A 0 (r + 2)).card) :
      (chordResidueGroup B 0 r).card + (chordResidueGroup B 0 (r + 2)).card ≤ 1 ∧
      (4 ≤ (chordResidueGroup A 0 r).card + (chordResidueGroup A 0 (r + 2)).card →
        (chordResidueGroup B 0 r).card + (chordResidueGroup B 0 (r + 2)).card = 0) := by
    have he := shared_residue_separated A B h6 h10 r hr
    exact ⟨four_group_high_shared_capacity _ _ _ _
      (residue_no_four_step A hA r) (residue_no_four_step A hA (r + 2))
      (residue_no_four_step B hB r) (residue_no_four_step B hB (r + 2)) he.1 he.2 ha,
      fun hh => four_group_quad_shared_empty _ _ _ _
        (residue_no_four_step A hA r) (residue_no_four_step A hA (r + 2)) he.1 he.2 hh⟩
  rcases hb with hb | hb
  · have ae1 := residue_empty_of_parity A b hpA 1 (by change 1 % 2 ≠ b; omega)
    have ae3 := residue_empty_of_parity A b hpA 3 (by change 3 % 2 ≠ b; omega)
    have be1 := residue_empty_of_parity B b hpB 1 (by change 1 % 2 ≠ b; omega)
    have be3 := residue_empty_of_parity B b hpB 3 (by change 3 % 2 ≠ b; omega)
    rw [ae1, ae3, Finset.card_empty] at ac
    rw [be1, be3, Finset.card_empty] at bc
    have h02 : (0 : Fin 4) + 2 = 2 := by
      apply Fin.ext
      rfl
    have hh := core 0 (Or.inl rfl) (by
      rw [h02]
      omega)
    rw [h02] at hh
    constructor
    · omega
    · intro hh4
      have hz := hh.2 (by omega)
      omega
  · have ae0 := residue_empty_of_parity A b hpA 0 (by change 0 % 2 ≠ b; omega)
    have ae2 := residue_empty_of_parity A b hpA 2 (by change 2 % 2 ≠ b; omega)
    have be0 := residue_empty_of_parity B b hpB 0 (by change 0 % 2 ≠ b; omega)
    have be2 := residue_empty_of_parity B b hpB 2 (by change 2 % 2 ≠ b; omega)
    rw [ae0, ae2, Finset.card_empty] at ac
    rw [be0, be2, Finset.card_empty] at bc
    have h13 : (1 : Fin 4) + 2 = 3 := by
      apply Fin.ext
      rfl
    have hh := core 1 (Or.inr rfl) (by
      rw [h13]
      omega)
    rw [h13] at hh
    constructor
    · omega
    · intro hh4
      have hz := hh.2 (by omega)
      omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.EarSeparated
#print axioms TaskH.Seven.BP.EarSeparatedBack
#print axioms TaskH.Seven.BP.earSeparated_two_forces_empty
#print axioms TaskH.Seven.BP.earSeparated_nonempty_card
#print axioms TaskH.Seven.BP.earSeparatedBack_two_forces_empty
#print axioms TaskH.Seven.BP.earSeparatedBack_nonempty_card
#print axioms TaskH.Seven.BP.four_group_high_shared_capacity
#print axioms TaskH.Seven.BP.four_group_quad_shared_empty
#print axioms TaskH.Seven.BP.residue_no_four_step
#print axioms TaskH.Seven.BP.shared_residue_separated
#print axioms TaskH.Seven.BP.same_parity_shared_high_capacity
