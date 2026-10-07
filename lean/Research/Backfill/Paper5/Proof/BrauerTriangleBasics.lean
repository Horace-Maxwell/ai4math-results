import Research.Backfill.Paper5.Proof.HalfDiagonal

set_option autoImplicit false

namespace CodexPaper5.BrauerTriangleBasics

open BackfillPaper5

/-- An even tail offset cannot be the last index of the even-length tail. -/
theorem r0_even_step_bound (n r : ℕ) (_hn : r + 2 ≤ n) (hpar : n % 2 = r % 2)
    (a : Fin n) (ht : r + 2 ≤ a.val) (he : (a.val - (r + 2)) % 2 = 0) :
    a.val + 1 < n := by
  have ha := a.isLt
  omega

theorem r0_of_lt (n r : ℕ) (a : Fin n) (ha : a.val < r + 2) :
    Challenge.r0 n r a = a := by
  have ht : ¬ r + 2 ≤ a.val := by omega
  simp only [Challenge.r0, ite_eq_right ht]

/-- The actual even branch takes its successor, with the frozen fallback excluded. -/
theorem r0_val_of_tail_even (n r : ℕ) (hn : r + 2 ≤ n) (hpar : n % 2 = r % 2)
    (a : Fin n) (ht : r + 2 ≤ a.val) (he : (a.val - (r + 2)) % 2 = 0) :
    (Challenge.r0 n r a).val = a.val + 1 := by
  have hb := r0_even_step_bound n r hn hpar a ht he
  simp only [Challenge.r0, ite_eq_left ht, ite_eq_left he, dite_eq_left hb]

theorem r0_val_of_tail_odd (n r : ℕ) (a : Fin n) (ht : r + 2 ≤ a.val)
    (he : (a.val - (r + 2)) % 2 ≠ 0) :
    (Challenge.r0 n r a).val = a.val - 1 := by
  simp only [Challenge.r0, ite_eq_left ht, ite_eq_right he]

/-- Both actual tail branches remain in the tail. -/
theorem r0_preserves_tail (n r : ℕ) (hn : r + 2 ≤ n) (hpar : n % 2 = r % 2)
    (a : Fin n) (ht : r + 2 ≤ a.val) : r + 2 ≤ (Challenge.r0 n r a).val := by
  by_cases he : (a.val - (r + 2)) % 2 = 0
  · rw [r0_val_of_tail_even n r hn hpar a ht he]
    omega
  · rw [r0_val_of_tail_odd n r a ht he]
    omega

/-- The entire frozen function is an involution, including the empty-tail case. -/
theorem r0_involutive (n r : ℕ) (hn : r + 2 ≤ n) (hpar : n % 2 = r % 2) :
    Function.Involutive (Challenge.r0 n r) := by
  intro a
  by_cases ht : r + 2 ≤ a.val
  · by_cases he : (a.val - (r + 2)) % 2 = 0
    · have hv := r0_val_of_tail_even n r hn hpar a ht he
      have ht' : r + 2 ≤ (Challenge.r0 n r a).val := by omega
      have he' : ((Challenge.r0 n r a).val - (r + 2)) % 2 ≠ 0 := by omega
      have hback := r0_val_of_tail_odd n r (Challenge.r0 n r a) ht' he'
      apply Fin.ext
      rw [hback, hv]
      omega
    · have hv := r0_val_of_tail_odd n r a ht he
      have ht' : r + 2 ≤ (Challenge.r0 n r a).val := by omega
      have he' : ((Challenge.r0 n r a).val - (r + 2)) % 2 = 0 := by omega
      have hback := r0_val_of_tail_even n r hn hpar (Challenge.r0 n r a) ht' he'
      apply Fin.ext
      rw [hback, hv]
      omega
  · have hlt : a.val < r + 2 := by omega
    simp only [r0_of_lt n r a hlt]

theorem r0_ne_of_tail (n r : ℕ) (hn : r + 2 ≤ n) (hpar : n % 2 = r % 2)
    (a : Fin n) (ht : r + 2 ≤ a.val) : Challenge.r0 n r a ≠ a := by
  intro h
  have hv := congrArg Fin.val h
  by_cases he : (a.val - (r + 2)) % 2 = 0
  · rw [r0_val_of_tail_even n r hn hpar a ht he] at hv
    omega
  · rw [r0_val_of_tail_odd n r a ht he] at hv
    omega

theorem triPartner_pos (j : Fin 3) : 0 < Challenge.triPartner j := by
  fin_cases j <;> decide

theorem triPartner_le_three (j : Fin 3) : Challenge.triPartner j ≤ 3 := by
  fin_cases j <;> decide

theorem triPartner_lt_prefix (r : ℕ) (hr : r = 2 ∨ r = 3) (j : Fin 3) :
    Challenge.triPartner j < r + 2 := by
  have hp := triPartner_le_three j
  omega

theorem triPartner_lt_n (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (j : Fin 3) : Challenge.triPartner j < n := by
  have hp := triPartner_lt_prefix r hr j
  omega

theorem triHalf_free_iff (n r : ℕ) (j : Fin 3) (a : Fin n) :
    a ∈ (Challenge.triHalf n r j).1 ↔
      a.val < r + 2 ∧ a.val ≠ 0 ∧ a.val ≠ Challenge.triPartner j := by
  simp only [Challenge.triHalf, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The actual zero-to-partner branch never uses its fallback. -/
theorem triHalf_match_zero_val (n r : ℕ) (hr : r = 2 ∨ r = 3)
    (hn : r + 2 ≤ n) (j : Fin 3) (a : Fin n) (ha : a.val = 0) :
    ((Challenge.triHalf n r j).2 a).val = Challenge.triPartner j := by
  have hp := triPartner_lt_n n r hr hn j
  simp only [Challenge.triHalf, ite_eq_left ha, dite_eq_left hp]

/-- The actual partner-to-zero branch never uses its fallback. -/
theorem triHalf_match_partner_val (n r : ℕ) (hr : r = 2 ∨ r = 3)
    (hn : r + 2 ≤ n) (j : Fin 3) (a : Fin n) (ha : a.val = Challenge.triPartner j) :
    ((Challenge.triHalf n r j).2 a).val = 0 := by
  have hp := triPartner_pos j
  have h0 : a.val ≠ 0 := by omega
  have hn0 : 0 < n := hp.trans (triPartner_lt_n n r hr hn j)
  simp only [Challenge.triHalf, ite_eq_right h0, ite_eq_left ha, dite_eq_left hn0]

theorem triHalf_match_other (n r : ℕ) (j : Fin 3) (a : Fin n)
    (h0 : a.val ≠ 0) (hp : a.val ≠ Challenge.triPartner j) :
    (Challenge.triHalf n r j).2 a = Challenge.r0 n r a := by
  simp only [Challenge.triHalf, ite_eq_right h0, ite_eq_right hp]

theorem triHalf_fixed_free (n r : ℕ) (j : Fin 3) (a : Fin n)
    (ha : a ∈ (Challenge.triHalf n r j).1) : (Challenge.triHalf n r j).2 a = a := by
  obtain ⟨hlt, h0, hp⟩ := (triHalf_free_iff n r j a).mp ha
  exact (triHalf_match_other n r j a h0 hp).trans (r0_of_lt n r a hlt)

/-- The two prefix swaps and the frozen tail involution act on disjoint regions. -/
theorem triHalf_involutive (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (j : Fin 3) :
    Function.Involutive (Challenge.triHalf n r j).2 := by
  intro a
  by_cases h0 : a.val = 0
  · have hv := triHalf_match_zero_val n r hr hn j a h0
    have hback := triHalf_match_partner_val n r hr hn j
      ((Challenge.triHalf n r j).2 a) hv
    apply Fin.ext
    exact hback.trans h0.symm
  · by_cases hp : a.val = Challenge.triPartner j
    · have hv := triHalf_match_partner_val n r hr hn j a hp
      have hback := triHalf_match_zero_val n r hr hn j
        ((Challenge.triHalf n r j).2 a) hv
      apply Fin.ext
      exact hback.trans hp.symm
    · by_cases ht : r + 2 ≤ a.val
      · have hb := r0_preserves_tail n r hn hpar a ht
        have hcp := triPartner_lt_prefix r hr j
        have hb0 : (Challenge.r0 n r a).val ≠ 0 := by omega
        have hbp : (Challenge.r0 n r a).val ≠ Challenge.triPartner j := by omega
        rw [triHalf_match_other n r j a h0 hp,
          triHalf_match_other n r j (Challenge.r0 n r a) hb0 hbp]
        exact r0_involutive n r hn hpar a
      · have hlt : a.val < r + 2 := by omega
        have hf : (Challenge.triHalf n r j).2 a = a :=
          (triHalf_match_other n r j a h0 hp).trans (r0_of_lt n r a hlt)
        simp only [hf]

theorem triHalf_ne_nonfree (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (j : Fin 3) (a : Fin n)
    (ha : a ∉ (Challenge.triHalf n r j).1) : (Challenge.triHalf n r j).2 a ≠ a := by
  have hpos := triPartner_pos j
  by_cases h0 : a.val = 0
  · intro heq
    have hv := congrArg Fin.val heq
    rw [triHalf_match_zero_val n r hr hn j a h0] at hv
    omega
  · by_cases hp : a.val = Challenge.triPartner j
    · intro heq
      have hv := congrArg Fin.val heq
      rw [triHalf_match_partner_val n r hr hn j a hp] at hv
      omega
    · have ht : r + 2 ≤ a.val := by
        by_contra hnot
        exact ha ((triHalf_free_iff n r j a).mpr ⟨by omega, h0, hp⟩)
      rw [triHalf_match_other n r j a h0 hp]
      exact r0_ne_of_tail n r hn hpar a ht

theorem triHalf_free_two_0 (n : ℕ) (hn : 4 ≤ n) :
    (Challenge.triHalf n 2 0).1 =
      {⟨2, by omega⟩, ⟨3, by omega⟩} := by
  apply Finset.ext
  intro a
  rw [triHalf_free_iff]
  simp only [Challenge.triPartner, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem triHalf_free_two_1 (n : ℕ) (hn : 4 ≤ n) :
    (Challenge.triHalf n 2 1).1 =
      {⟨1, by omega⟩, ⟨3, by omega⟩} := by
  apply Finset.ext
  intro a
  rw [triHalf_free_iff]
  simp only [Challenge.triPartner, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem triHalf_free_two_2 (n : ℕ) (hn : 4 ≤ n) :
    (Challenge.triHalf n 2 2).1 =
      {⟨1, by omega⟩, ⟨2, by omega⟩} := by
  apply Finset.ext
  intro a
  rw [triHalf_free_iff]
  simp only [Challenge.triPartner, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem triHalf_free_three_0 (n : ℕ) (hn : 5 ≤ n) :
    (Challenge.triHalf n 3 0).1 =
      {⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩} := by
  apply Finset.ext
  intro a
  rw [triHalf_free_iff]
  simp only [Challenge.triPartner, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem triHalf_free_three_1 (n : ℕ) (hn : 5 ≤ n) :
    (Challenge.triHalf n 3 1).1 =
      {⟨1, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩} := by
  apply Finset.ext
  intro a
  rw [triHalf_free_iff]
  simp only [Challenge.triPartner, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem triHalf_free_three_2 (n : ℕ) (hn : 5 ≤ n) :
    (Challenge.triHalf n 3 2).1 =
      {⟨1, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩} := by
  apply Finset.ext
  intro a
  rw [triHalf_free_iff]
  simp only [Challenge.triPartner, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  omega

theorem triHalf_card (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (j : Fin 3) : (Challenge.triHalf n r j).1.card = r := by
  rcases hr with rfl | rfl
  · have hn4 : 4 ≤ n := by omega
    fin_cases j
    · change (Challenge.triHalf n 2 0).1.card = 2
      rw [triHalf_free_two_0 n hn4]
      simp [Fin.ext_iff]
    · change (Challenge.triHalf n 2 1).1.card = 2
      rw [triHalf_free_two_1 n hn4]
      simp [Fin.ext_iff]
    · change (Challenge.triHalf n 2 2).1.card = 2
      rw [triHalf_free_two_2 n hn4]
      simp [Fin.ext_iff]
  · have hn5 : 5 ≤ n := by omega
    fin_cases j
    · change (Challenge.triHalf n 3 0).1.card = 3
      rw [triHalf_free_three_0 n hn5]
      simp [Fin.ext_iff]
    · change (Challenge.triHalf n 3 1).1.card = 3
      rw [triHalf_free_three_1 n hn5]
      simp [Fin.ext_iff]
    · change (Challenge.triHalf n 3 2).1.card = 3
      rw [triHalf_free_three_2 n hn5]
      simp [Fin.ext_iff]

/-- All three frozen half-diagrams are fully legal for every allowed n, including empty tails. -/
theorem triHalf_mem_hr (n r : ℕ) (hr : r = 2 ∨ r = 3) (hn : r + 2 ≤ n)
    (hpar : n % 2 = r % 2) (j : Fin 3) :
    Challenge.triHalf n r j ∈ Challenge.Hr Challenge.Fam.B n r := by
  exact ⟨triHalf_card n r hr hn j, triHalf_involutive n r hr hn hpar j,
    fun a ha => triHalf_fixed_free n r j a ha,
    fun _hB a ha => triHalf_ne_nonfree n r hr hn hpar j a ha⟩

#print axioms CodexPaper5.BrauerTriangleBasics.r0_even_step_bound
#print axioms CodexPaper5.BrauerTriangleBasics.r0_of_lt
#print axioms CodexPaper5.BrauerTriangleBasics.r0_val_of_tail_even
#print axioms CodexPaper5.BrauerTriangleBasics.r0_val_of_tail_odd
#print axioms CodexPaper5.BrauerTriangleBasics.r0_preserves_tail
#print axioms CodexPaper5.BrauerTriangleBasics.r0_involutive
#print axioms CodexPaper5.BrauerTriangleBasics.r0_ne_of_tail
#print axioms CodexPaper5.BrauerTriangleBasics.triPartner_pos
#print axioms CodexPaper5.BrauerTriangleBasics.triPartner_le_three
#print axioms CodexPaper5.BrauerTriangleBasics.triPartner_lt_prefix
#print axioms CodexPaper5.BrauerTriangleBasics.triPartner_lt_n
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_free_iff
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_match_zero_val
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_match_partner_val
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_match_other
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_fixed_free
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_involutive
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_ne_nonfree
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_free_two_0
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_free_two_1
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_free_two_2
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_free_three_0
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_free_three_1
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_free_three_2
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_card
#print axioms CodexPaper5.BrauerTriangleBasics.triHalf_mem_hr

end CodexPaper5.BrauerTriangleBasics
