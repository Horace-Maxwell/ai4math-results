import Research.Backfill.Paper7.C61AlternatingQpositiveBound

/-! NEW SOURCE ONLY. Complete cyclic-position coverage for the generic bound. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three
open scoped BigOperators Classical

theorem odd_zero_qpositive_total_bound (p q : Fin 6 → ℕ) (C : ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hw : FullUnitWitness p q) (hm : PairTwo p q)
    (hl : ∀ k, p k + q k ≤ C) (hq : ∃ k, 0 < q k) :
    totalP 6 p + totalQ 6 q = 9 ∨ totalP 6 p + totalQ 6 q ≤ C + 4 := by
  let p2 := shiftSix (shiftSix p)
  let q2 := shiftSix (shiftSix q)
  let p4 := shiftSix (shiftSix p2)
  let q4 := shiftSix (shiftSix q2)
  have hw2 : FullUnitWitness p2 q2 :=
    full_unit_witness_shift _ _ (full_unit_witness_shift _ _ hw)
  have hw4 : FullUnitWitness p4 q4 :=
    full_unit_witness_shift _ _ (full_unit_witness_shift _ _ hw2)
  have hm2 : PairTwo p2 q2 := pair_two_shift _ _ (pair_two_shift _ _ hm)
  have hm4 : PairTwo p4 q4 := pair_two_shift _ _ (pair_two_shift _ _ hm2)
  have hl2 : ∀ k, p2 k + q2 k ≤ C := fun k => hl ((k + 1) + 1)
  have hl4 : ∀ k, p4 k + q4 k ≤ C := fun k => hl2 ((k + 1) + 1)
  have hp21 : p2 1 = 0 := by simpa [p2, shiftSix] using hp3
  have hp23 : p2 3 = 0 := by simpa [p2, shiftSix] using hp5
  have hp25 : p2 5 = 0 := by simpa [p2, shiftSix] using hp1
  have hp41 : p4 1 = 0 := by simpa [p4, p2, shiftSix] using hp5
  have hp43 : p4 3 = 0 := by simpa [p4, p2, shiftSix] using hp1
  have hp45 : p4 5 = 0 := by simpa [p4, p2, shiftSix] using hp3
  have hq0 : q 0 = 0 := by
    by_contra hn
    exact odd_zero_even_q_impossible p q hp1 hp3 hp5 hw hm (Nat.pos_of_ne_zero hn)
  have hq2 : q 2 = 0 := by
    by_contra hn
    apply odd_zero_even_q_impossible p2 q2 hp21 hp23 hp25 hw2 hm2
    simpa [q2, shiftSix] using Nat.pos_of_ne_zero hn
  have hq4 : q 4 = 0 := by
    by_contra hn
    apply odd_zero_even_q_impossible p4 q4 hp41 hp43 hp45 hw4 hm4
    simpa [q4, q2, shiftSix] using Nat.pos_of_ne_zero hn
  obtain ⟨k, hk⟩ := hq
  fin_cases k
  · simp [hq0] at hk
  · exact odd_zero_q_one_total_bound p q C hp1 hp3 hp5 hq0 hq2 hq4 hw hm hl hk
  · simp [hq2] at hk
  · change 0 < q (3 : Fin 6) at hk
    have h := odd_zero_q_one_total_bound p2 q2 C hp21 hp23 hp25
      (by simpa [q2, shiftSix] using hq2)
      (by simpa [q2, shiftSix] using hq4)
      (by simpa [q2, shiftSix] using hq0) hw2 hm2 hl2
      (by simpa [q2, shiftSix] using hk)
    simpa [p2, q2, total_shift] using h
  · simp [hq4] at hk
  · change 0 < q (5 : Fin 6) at hk
    have h := odd_zero_q_one_total_bound p4 q4 C hp41 hp43 hp45
      (by simpa [q4, q2, shiftSix] using hq4)
      (by simpa [q4, q2, shiftSix] using hq0)
      (by simpa [q4, q2, shiftSix] using hq2) hw4 hm4 hl4
      (by simpa [q4, q2, shiftSix] using hk)
    simpa [p4, q4, p2, q2, total_shift] using h
#print axioms Paper7C61Four.odd_zero_qpositive_total_bound

theorem alternating_qpositive_total_bound (p q : Fin 6 → ℕ) (C : ℕ)
    (hp : (p 1 = 0 ∧ p 3 = 0 ∧ p 5 = 0) ∨ (p 0 = 0 ∧ p 2 = 0 ∧ p 4 = 0))
    (hw : FullUnitWitness p q) (hm : PairTwo p q)
    (hl : ∀ k, p k + q k ≤ C) (hq : ∃ k, 0 < q k) :
    totalP 6 p + totalQ 6 q = 9 ∨ totalP 6 p + totalQ 6 q ≤ C + 4 := by
  rcases hp with hp | hp
  · exact odd_zero_qpositive_total_bound p q C hp.1 hp.2.1 hp.2.2 hw hm hl hq
  · have hq' : ∃ k, 0 < shiftSix q k := by
      obtain ⟨k, hk⟩ := hq
      refine ⟨k + 5, ?_⟩
      simpa [shiftSix, add_assoc] using hk
    have h := odd_zero_qpositive_total_bound (shiftSix p) (shiftSix q) C
      (by simpa [shiftSix] using hp.2.1)
      (by simpa [shiftSix] using hp.2.2)
      (by simpa [shiftSix] using hp.1)
      (full_unit_witness_shift p q hw) (pair_two_shift p q hm)
      (fun k => hl (k + 1)) hq'
    simpa [total_shift] using h
#print axioms Paper7C61Four.alternating_qpositive_total_bound

end Paper7C61Four
