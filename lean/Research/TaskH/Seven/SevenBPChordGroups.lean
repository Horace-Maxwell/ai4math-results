import Research.TaskH.Seven.SevenBPChordExclusions

/-! Pure modulo-four support counting. The finite checks concern subsets
of four group positions, not graphs or arbitrary chord configurations. -/

set_option autoImplicit false

namespace TaskH.Seven.BP

def GroupSeparated (A C : Finset (Fin 4)) : Prop :=
  ∀ t : Fin 4, t ∈ A → t ∉ C ∧ t + 3 ∉ C

theorem groupSeparated_card (A C : Finset (Fin 4)) (h : GroupSeparated A C) :
    A.card + C.card ≤ 4 := by
  have ht : ∀ A C : Finset (Fin 4), GroupSeparated A C → A.card + C.card ≤ 4 := by
    unfold GroupSeparated
    decide +kernel
  exact ht A C h

theorem groupSeparated_eq_four (A C : Finset (Fin 4)) (h : GroupSeparated A C)
    (hc : A.card + C.card = 4) : A = Finset.univ ∨ C = Finset.univ := by
  have ht : ∀ A C : Finset (Fin 4), GroupSeparated A C →
      A.card + C.card = 4 → A = Finset.univ ∨ C = Finset.univ := by
    unfold GroupSeparated
    decide +kernel
  exact ht A C h hc

theorem groupSeparated_full_left (A C : Finset (Fin 4)) (h : GroupSeparated A C)
    (ha : A = Finset.univ) : C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact (h t (by rw [ha]; exact Finset.mem_univ t)).1 ht

theorem groupSeparated_full_right (A C : Finset (Fin 4)) (h : GroupSeparated A C)
    (hc : C = Finset.univ) : A = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact (h t ht).1 (by rw [hc]; exact Finset.mem_univ t)

theorem four_groups_no_adjacent_card (A : Finset (Fin 4))
    (h : ∀ t : Fin 4, t ∈ A → t + 1 ∉ A) : A.card ≤ 2 := by
  have ht : ∀ A : Finset (Fin 4),
      (∀ t : Fin 4, t ∈ A → t + 1 ∉ A) → A.card ≤ 2 := by
    decide +kernel
  exact ht A h

def FiveGroupRestrictions (A B C D : Finset (Fin 4)) : Prop :=
  GroupSeparated A C ∧ GroupSeparated B D ∧
  (∀ t : Fin 4, t ∈ A → t ∈ B → t + 1 ∉ A) ∧
  (∀ t : Fin 4, t ∈ B → t ∈ C → t + 1 ∉ B) ∧
  (∀ t : Fin 4, t ∈ C → t ∈ D → t + 1 ∉ C) ∧
  (∀ t : Fin 4, t ∈ D → t + 1 ∈ A → t + 1 ∉ D)

theorem five_groups_card_le_six (A B C D : Finset (Fin 4))
    (h : FiveGroupRestrictions A B C D) : A.card + B.card + C.card + D.card ≤ 6 := by
  classical
  rcases h with ⟨hAC, hBD, hAB, hBC, hCD, hDA⟩
  have hp := groupSeparated_card A C hAC
  have hq := groupSeparated_card B D hBD
  by_contra hnot
  have hfull : A = Finset.univ ∨ B = Finset.univ ∨
      C = Finset.univ ∨ D = Finset.univ := by
    have he : A.card + C.card = 4 ∨ B.card + D.card = 4 := by omega
    rcases he with he | he
    · rcases groupSeparated_eq_four A C hAC he with ha | hc
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl hc))
    · rcases groupSeparated_eq_four B D hBD he with hb | hd
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Or.inr hd))
  rcases hfull with ha | hb | hc | hd
  · have hc := groupSeparated_full_left A C hAC ha
    have hb : B = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hAB t (by rw [ha]; exact Finset.mem_univ t) ht
        (by rw [ha]; exact Finset.mem_univ _)
    have hd2 : D.card ≤ 2 := four_groups_no_adjacent_card D (by
      intro t ht
      exact hDA t ht (by rw [ha]; exact Finset.mem_univ _))
    have ha4 : A.card = 4 := by rw [ha]; decide
    have hb0 : B.card = 0 := by rw [hb]; rfl
    have hc0 : C.card = 0 := by rw [hc]; rfl
    omega
  · have hd := groupSeparated_full_left B D hBD hb
    have hc : C = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hBC t (by rw [hb]; exact Finset.mem_univ t) ht
        (by rw [hb]; exact Finset.mem_univ _)
    have ha2 : A.card ≤ 2 := four_groups_no_adjacent_card A (by
      intro t ht
      exact hAB t ht (by rw [hb]; exact Finset.mem_univ _))
    have hb4 : B.card = 4 := by rw [hb]; decide
    have hc0 : C.card = 0 := by rw [hc]; rfl
    have hd0 : D.card = 0 := by rw [hd]; rfl
    omega
  · have ha := groupSeparated_full_right A C hAC hc
    have hd : D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      exact hCD t (by rw [hc]; exact Finset.mem_univ t) ht
        (by rw [hc]; exact Finset.mem_univ _)
    have hb2 : B.card ≤ 2 := four_groups_no_adjacent_card B (by
      intro t ht
      exact hBC t ht (by rw [hc]; exact Finset.mem_univ _))
    have ha0 : A.card = 0 := by rw [ha]; rfl
    have hc4 : C.card = 4 := by rw [hc]; decide
    have hd0 : D.card = 0 := by rw [hd]; rfl
    omega
  · have hb := groupSeparated_full_right B D hBD hd
    have ha : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have he : (t + 3) + 1 = t := by
        have hk : ∀ t : Fin 4, (t + 3) + 1 = t := by decide +kernel
        exact hk t
      have ht' : (t + 3) + 1 ∈ A := by simpa only [he] using ht
      exact hDA (t + 3) (by rw [hd]; exact Finset.mem_univ _) ht'
        (by rw [hd]; exact Finset.mem_univ _)
    have hc2 : C.card ≤ 2 := four_groups_no_adjacent_card C (by
      intro t ht
      exact hCD t ht (by rw [hd]; exact Finset.mem_univ _))
    have ha0 : A.card = 0 := by rw [ha]; rfl
    have hb0 : B.card = 0 := by rw [hb]; rfl
    have hd4 : D.card = 4 := by rw [hd]; decide
    omega

def allowedZero (J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun t => t ∉ J ∧ t + 3 ∉ J)

def allowedThree (I : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun t => t ∉ I ∧ t + 1 ∉ I)

def allowedMiddle (I J : Finset (Fin 4)) : Finset (Fin 4) :=
  Finset.univ.filter (fun t => ∀ k ∈ I ∩ J, t.val % 2 = k.val % 2)

theorem normalized_six_group_capacity (I J : Finset (Fin 4))
    (hf : 6 ≤ I.card + J.card) :
    (allowedZero J).card + 2 * (allowedMiddle I J).card + (allowedThree I).card ≤ 4 := by
  have ht : ∀ I J : Finset (Fin 4), 6 ≤ I.card + J.card →
      (allowedZero J).card + 2 * (allowedMiddle I J).card +
        (allowedThree I).card ≤ 4 := by
    unfold allowedZero allowedThree allowedMiddle
    decide +kernel
  exact ht I J hf

theorem normalized_seven_group_capacity (I J : Finset (Fin 4))
    (hf : 7 ≤ I.card + J.card) :
    (allowedZero J).card + 2 * (allowedMiddle I J).card + (allowedThree I).card = 0 := by
  have ht : ∀ I J : Finset (Fin 4), 7 ≤ I.card + J.card →
      (allowedZero J).card + 2 * (allowedMiddle I J).card +
        (allowedThree I).card = 0 := by
    unfold allowedZero allowedThree allowedMiddle
    decide +kernel
  exact ht I J hf

theorem normalized_chord_total_le_eleven (A B C D I J : Finset (Fin 4))
    (hE : FiveGroupRestrictions A B C D)
    (hA : A ⊆ allowedZero J) (hD : D ⊆ allowedThree I)
    (hB : B ⊆ allowedMiddle I J) (hC : C ⊆ allowedMiddle I J) :
    A.card + B.card + C.card + D.card + I.card + J.card ≤ 11 := by
  have he := five_groups_card_le_six A B C D hE
  have hi : I.card ≤ 4 := by simpa using Finset.card_le_univ I
  have hj : J.card ≤ 4 := by simpa using Finset.card_le_univ J
  by_cases hf : I.card + J.card ≤ 5
  · omega
  · have hf6 : 6 ≤ I.card + J.card := by omega
    have ha := Finset.card_le_card hA
    have hd := Finset.card_le_card hD
    have hb := Finset.card_le_card hB
    have hc := Finset.card_le_card hC
    by_cases hf7 : 7 ≤ I.card + J.card
    · have hz := normalized_seven_group_capacity I J hf7
      omega
    · have hcap := normalized_six_group_capacity I J hf6
      omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.GroupSeparated
#print axioms TaskH.Seven.BP.groupSeparated_card
#print axioms TaskH.Seven.BP.groupSeparated_eq_four
#print axioms TaskH.Seven.BP.groupSeparated_full_left
#print axioms TaskH.Seven.BP.groupSeparated_full_right
#print axioms TaskH.Seven.BP.four_groups_no_adjacent_card
#print axioms TaskH.Seven.BP.FiveGroupRestrictions
#print axioms TaskH.Seven.BP.five_groups_card_le_six
#print axioms TaskH.Seven.BP.allowedZero
#print axioms TaskH.Seven.BP.allowedThree
#print axioms TaskH.Seven.BP.allowedMiddle
#print axioms TaskH.Seven.BP.normalized_six_group_capacity
#print axioms TaskH.Seven.BP.normalized_seven_group_capacity
#print axioms TaskH.Seven.BP.normalized_chord_total_le_eleven
