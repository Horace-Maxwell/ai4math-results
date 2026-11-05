import Research.Backfill.Paper7.C61FourThreeCardPositions

/-! NEW SOURCE ONLY. All cyclic positions and both support parities. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge Paper7C61Three
open scoped Classical

theorem odd_zero_three_card_qpositive_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hw : FullUnitWitness p q) (hd : ThreeCardData p q)
    (hl : ∀ k, p k + q k ≤ 13) (hq : ∃ k, 0 < q k) : False := by
  let p2 := shiftSix (shiftSix p)
  let q2 := shiftSix (shiftSix q)
  let p4 := shiftSix (shiftSix p2)
  let q4 := shiftSix (shiftSix q2)
  have hw2 : FullUnitWitness p2 q2 :=
    full_unit_witness_shift _ _ (full_unit_witness_shift _ _ hw)
  have hw4 : FullUnitWitness p4 q4 :=
    full_unit_witness_shift _ _ (full_unit_witness_shift _ _ hw2)
  have hd2 : ThreeCardData p2 q2 := three_card_data_shift _ _ (three_card_data_shift _ _ hd)
  have hd4 : ThreeCardData p4 q4 := three_card_data_shift _ _ (three_card_data_shift _ _ hd2)
  have hl2 : ∀ k, p2 k + q2 k ≤ 13 := fun k => hl ((k + 1) + 1)
  have hl4 : ∀ k, p4 k + q4 k ≤ 13 := fun k => hl2 ((k + 1) + 1)
  have hp21 : p2 1 = 0 := by simpa [p2, shiftSix] using hp3
  have hp23 : p2 3 = 0 := by simpa [p2, shiftSix] using hp5
  have hp25 : p2 5 = 0 := by simpa [p2, shiftSix] using hp1
  have hp41 : p4 1 = 0 := by simpa [p4, p2, shiftSix] using hp5
  have hp43 : p4 3 = 0 := by simpa [p4, p2, shiftSix] using hp1
  have hp45 : p4 5 = 0 := by simpa [p4, p2, shiftSix] using hp3
  have hq0 : q 0 = 0 := by
    by_contra hn
    exact three_card_even_q_impossible p q hp1 hp3 hp5 hw hl hd (Nat.pos_of_ne_zero hn)
  have hq2 : q 2 = 0 := by
    by_contra hn
    apply three_card_even_q_impossible p2 q2 hp21 hp23 hp25 hw2 hl2 hd2
    simpa [q2, shiftSix] using Nat.pos_of_ne_zero hn
  have hq4 : q 4 = 0 := by
    by_contra hn
    apply three_card_even_q_impossible p4 q4 hp41 hp43 hp45 hw4 hl4 hd4
    simpa [q4, q2, shiftSix] using Nat.pos_of_ne_zero hn
  obtain ⟨k, hk⟩ := hq
  fin_cases k
  · simp [hq0] at hk
  · exact three_card_odd_q_one_impossible p q hp1 hp3 hp5 hq0 hq2 hq4 hw hl hd hk
  · simp [hq2] at hk
  · change 0 < q (3 : Fin 6) at hk
    apply three_card_odd_q_one_impossible p2 q2 hp21 hp23 hp25
      (by simpa [q2, shiftSix] using hq2)
      (by simpa [q2, shiftSix] using hq4)
      (by simpa [q2, shiftSix] using hq0) hw2 hl2 hd2
    simpa [q2, shiftSix] using hk
  · simp [hq4] at hk
  · change 0 < q (5 : Fin 6) at hk
    apply three_card_odd_q_one_impossible p4 q4 hp41 hp43 hp45
      (by simpa [q4, q2, shiftSix] using hq4)
      (by simpa [q4, q2, shiftSix] using hq0)
      (by simpa [q4, q2, shiftSix] using hq2) hw4 hl4 hd4
    simpa [q4, q2, shiftSix] using hk
#print axioms Paper7C61Four.odd_zero_three_card_qpositive_impossible

theorem alternating_three_card_qpositive_impossible (p q : Fin 6 → ℕ)
    (hp : (p 1 = 0 ∧ p 3 = 0 ∧ p 5 = 0) ∨ (p 0 = 0 ∧ p 2 = 0 ∧ p 4 = 0))
    (hw : FullUnitWitness p q) (hd : ThreeCardData p q)
    (hl : ∀ k, p k + q k ≤ 13) (hq : ∃ k, 0 < q k) : False := by
  rcases hp with hp | hp
  · exact odd_zero_three_card_qpositive_impossible p q hp.1 hp.2.1 hp.2.2 hw hd hl hq
  · apply odd_zero_three_card_qpositive_impossible (shiftSix p) (shiftSix q)
      (by simpa [shiftSix] using hp.2.1)
      (by simpa [shiftSix] using hp.2.2)
      (by simpa [shiftSix] using hp.1)
      (full_unit_witness_shift p q hw) (three_card_data_shift p q hd)
      (fun k => hl (k + 1))
    obtain ⟨k, hk⟩ := hq
    refine ⟨k + 5, ?_⟩
    simpa [shiftSix, add_assoc] using hk
#print axioms Paper7C61Four.alternating_three_card_qpositive_impossible

end Paper7C61Four
