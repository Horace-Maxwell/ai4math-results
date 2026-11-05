import Research.Backfill.Paper7.C61ThreeQpositivePositions

/-! NEW SOURCE ONLY. Rotation acts on recurrence witnesses and the three
monodromy consequences. No profile transport assumption is introduced. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Three
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Classical

theorem odd_zero_qpositive_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hw : FullUnitWitness p q) (hm : PairTwo p q)
    (hs : totalP 6 p + totalQ 6 q = 11)
    (hl : ∀ k, p k + q k ≤ 6) (hq : ∃ k, 0 < q k) : False := by
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
  have hs2 : totalP 6 p2 + totalQ 6 q2 = 11 := by
    dsimp only [p2, q2]
    rw [total_shift, total_shift, hs]
  have hs4 : totalP 6 p4 + totalQ 6 q4 = 11 := by
    dsimp only [p4, q4]
    rw [total_shift, total_shift, hs2]
  have hl2 : ∀ k, p2 k + q2 k ≤ 6 := fun k => hl ((k + 1) + 1)
  have hl4 : ∀ k, p4 k + q4 k ≤ 6 := fun k => hl2 ((k + 1) + 1)
  have hp21 : p2 1 = 0 := by simpa only [p2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp3
  have hp23 : p2 3 = 0 := by simpa only [p2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp5
  have hp25 : p2 5 = 0 := by simpa only [p2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp1
  have hp41 : p4 1 = 0 := by simpa only [p4, p2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp5
  have hp43 : p4 3 = 0 := by simpa only [p4, p2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp1
  have hp45 : p4 5 = 0 := by simpa only [p4, p2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp3
  have hq0 : q 0 = 0 := by
    by_contra hn
    exact odd_zero_even_q_impossible p q hp1 hp3 hp5 hw hm (Nat.pos_of_ne_zero hn)
  have hq2 : q 2 = 0 := by
    by_contra hn
    apply odd_zero_even_q_impossible p2 q2 hp21 hp23 hp25 hw2 hm2
    simpa only [q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using Nat.pos_of_ne_zero hn
  have hq4 : q 4 = 0 := by
    by_contra hn
    apply odd_zero_even_q_impossible p4 q4 hp41 hp43 hp45 hw4 hm4
    simpa only [q4, q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using Nat.pos_of_ne_zero hn
  obtain ⟨k, hk⟩ := hq
  fin_cases k
  · simp [hq0] at hk
  · exact odd_zero_q_one_impossible p q hp1 hp3 hp5 hq0 hq2 hq4 hw hm hs hl hk
  · simp [hq2] at hk
  · apply odd_zero_q_one_impossible p2 q2 hp21 hp23 hp25
      (by simpa only [q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hq2)
      (by simpa only [q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hq4)
      (by simpa only [q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hq0) hw2 hm2 hs2 hl2
    change 0 < q (3 : Fin 6) at hk
    simpa only [q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hk
  · simp [hq4] at hk
  · apply odd_zero_q_one_impossible p4 q4 hp41 hp43 hp45
      (by simpa only [q4, q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hq4)
      (by simpa only [q4, q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hq0)
      (by simpa only [q4, q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hq2) hw4 hm4 hs4 hl4
    change 0 < q (5 : Fin 6) at hk
    simpa only [q4, q2, shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hk
#print axioms Paper7C61Three.odd_zero_qpositive_impossible

theorem alternating_qpositive_impossible (p q : Fin 6 → ℕ)
    (hp : (p 1 = 0 ∧ p 3 = 0 ∧ p 5 = 0) ∨ (p 0 = 0 ∧ p 2 = 0 ∧ p 4 = 0))
    (hw : FullUnitWitness p q) (hm : PairTwo p q)
    (hs : totalP 6 p + totalQ 6 q = 11)
    (hl : ∀ k, p k + q k ≤ 6) (hq : ∃ k, 0 < q k) : False := by
  rcases hp with hp | hp
  · exact odd_zero_qpositive_impossible p q hp.1 hp.2.1 hp.2.2 hw hm hs hl hq
  · apply odd_zero_qpositive_impossible (shiftSix p) (shiftSix q)
      (by simpa only [shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp.2.1)
      (by simpa only [shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp.2.2)
      (by simpa only [shiftSix, show (0 : Fin 6) + 1 = 1 from rfl, show (1 : Fin 6) + 1 = 2 from rfl, show (2 : Fin 6) + 1 = 3 from rfl, show (3 : Fin 6) + 1 = 4 from rfl, show (4 : Fin 6) + 1 = 5 from rfl, show (5 : Fin 6) + 1 = 0 from rfl] using hp.1)
      (full_unit_witness_shift p q hw) (pair_two_shift p q hm)
      (by rw [total_shift]; exact hs) (fun k => hl (k + 1))
    obtain ⟨k, hk⟩ := hq
    refine ⟨k + 5, ?_⟩
    simpa [shiftSix, add_assoc] using hk
#print axioms Paper7C61Three.alternating_qpositive_impossible

end Paper7C61Three
