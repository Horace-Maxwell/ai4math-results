import Research.Backfill.Paper7.C61UnitWitnessShapes
import Research.Backfill.Paper7.C61TraceCountBounds

/-! NEW SOURCE ONLY. Complete local support cases for the two Perron-four
three-root profiles containing 3. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Three
open scoped Matrix BigOperators Classical

theorem sparse_transfer_trace (a d : ℝ) :
    (realSixProduct a 2 2 d 2 2).trace = 9*a*d-12*a-12*d+14 := by
  norm_num [realSixProduct, realTransfer, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring
#print axioms Paper7C61Four.sparse_transfer_trace

theorem alternating_transfer_trace (a b c : ℝ) :
    (realSixProduct (3/2) (2-2*a/3) (3/2) (2-2*b/3) (3/2) (2-2*c/3)).trace =
      (1-a)*(1-b)*(1-c)-(3-(a+b+c)) := by
  norm_num [realSixProduct, realTransfer, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring
#print axioms Paper7C61Four.alternating_transfer_trace

theorem three_card_sparse_zero_three_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp2 : p 2 = 0) (hp3 : p 3 = 0) (hp4 : p 4 = 0) (hp5 : p 5 = 0)
    (hq1 : q 1 = 0) (hq2 : q 2 = 0) (hq4 : q 4 = 0) (hq5 : q 5 = 0)
    (hl : ∀ k, p k + q k ≤ 13) (hd : ThreeCardData p q) : False := by
  have hl0 := hl 0
  have hl3 := hl 3
  rw [hp3, zero_add] at hl3
  rcases hd with ⟨ht, hs⟩ | ⟨_hm, hs⟩
  · norm_num [totalP, totalQ, Fin.sum_univ_succ,
      hp1, hp2, hp3, hp4, hp5, hq1, hq2, hq4, hq5] at hs
    unfold TraceTwo at ht
    norm_num [coefficientTwo, hp1, hp2, hp3, hp4, hp5, hq1, hq2, hq4, hq5] at ht
    rw [sparse_transfer_trace] at ht
    have hh : (3 * (p 0 : ℝ) + 4 * q 0) * ((q 3 : ℝ) - 1) = 4 * q 3 := by
      nlinarith only [ht]
    exact sparse_trace_sum_twenty_three_impossible (p 0) (q 0) (q 3) (by omega) hl0 hl3 hh
  · norm_num [totalP, totalQ, Fin.sum_univ_succ,
      hp1, hp2, hp3, hp4, hp5, hq1, hq2, hq4, hq5] at hs
    omega
#print axioms Paper7C61Four.three_card_sparse_zero_three_impossible

theorem three_card_even_q_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hw : FullUnitWitness p q) (hl : ∀ k, p k + q k ≤ 13)
    (hd : ThreeCardData p q) (hq0 : 0 < q 0) : False := by
  obtain ⟨hq1, hq2, hq4, hq5, hp2, hp4⟩ :=
    odd_zero_even_q_support p q hp1 hp3 hp5 hw hq0
  exact three_card_sparse_zero_three_impossible p q hp1 hp2 hp3 hp4 hp5
    hq1 hq2 hq4 hq5 hl hd
#print axioms Paper7C61Four.three_card_even_q_impossible

theorem three_card_alternating_ones_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hq0 : q 0 = 0) (hq2 : q 2 = 0) (hq4 : q 4 = 0)
    (hp0 : p 0 = 1) (hp2 : p 2 = 1) (hp4 : p 4 = 1)
    (hl : ∀ k, p k + q k ≤ 13) (hd : ThreeCardData p q) : False := by
  have hl1 : q 1 ≤ 13 := by have := hl 1; omega
  have hl3 : q 3 ≤ 13 := by have := hl 3; omega
  have hl5 : q 5 ≤ 13 := by have := hl 5; omega
  rcases hd with ⟨ht, hs⟩ | ⟨hm, hs⟩
  · unfold TraceTwo at ht
    norm_num [coefficientTwo, hp0, hp1, hp2, hp3, hp4, hp5, hq0, hq2, hq4] at ht
    rw [alternating_transfer_trace] at ht
    have hh : (1-(q 1 : ℝ))*(1-(q 3 : ℝ))*(1-(q 5 : ℝ)) =
        5-((q 1 : ℝ)+q 3+q 5) := by
      linarith
    have hb := trace_three_counts_le_seventeen (q 1) (q 3) (q 5) hl1 hl3 hl5 hh
    norm_num [totalP, totalQ, Fin.sum_univ_succ,
      hp0, hp1, hp2, hp3, hp4, hp5, hq0, hq2, hq4] at hs
    omega
  · obtain ⟨h0, h1, h2⟩ := hm
    norm_num [coefficientThree, hp0, hp1, hp2, hp3, hp4, hp5, hq0, hq2, hq4] at h0 h1 h2
    have hsR : (totalP 6 p : ℝ) + totalQ 6 q = 28 := by exact_mod_cast hs
    norm_num [totalP, totalQ, Fin.sum_univ_succ,
      hp0, hp1, hp2, hp3, hp4, hp5, hq0, hq2, hq4] at hsR
    linarith
#print axioms Paper7C61Four.three_card_alternating_ones_impossible

theorem three_card_odd_q_one_impossible (p q : Fin 6 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (hp5 : p 5 = 0)
    (hq0 : q 0 = 0) (hq2 : q 2 = 0) (hq4 : q 4 = 0)
    (hw : FullUnitWitness p q) (hl : ∀ k, p k + q k ≤ 13)
    (hd : ThreeCardData p q) (hq1 : 0 < q 1) : False := by
  rcases odd_zero_q_one_unit_shapes p q hp1 hp3 hp5 hq0 hq2 hq4 hw hq1 with
    ⟨hp0, hp2, hp4⟩ | ⟨hq3, hq5, hs⟩
  · exact three_card_alternating_ones_impossible p q hp1 hp3 hp5 hq0 hq2 hq4
      hp0 hp2 hp4 hl hd
  · rcases hs with ⟨hp0, hp2⟩ | hpSum
    · let p4 := shiftSix (shiftSix (shiftSix (shiftSix p)))
      let q4 := shiftSix (shiftSix (shiftSix (shiftSix q)))
      have hd4 : ThreeCardData p4 q4 := three_card_data_shift _ _
        (three_card_data_shift _ _ (three_card_data_shift _ _ (three_card_data_shift _ _ hd)))
      apply three_card_sparse_zero_three_impossible p4 q4
        (by simpa [p4, shiftSix] using hp5)
        (by simpa [p4, shiftSix] using hp0)
        (by simpa [p4, shiftSix] using hp1)
        (by simpa [p4, shiftSix] using hp2)
        (by simpa [p4, shiftSix] using hp3)
        (by simpa [q4, shiftSix] using hq5)
        (by simpa [q4, shiftSix] using hq0)
        (by simpa [q4, shiftSix] using hq2)
        (by simpa [q4, shiftSix] using hq3)
        (fun k => hl ((((k+1)+1)+1)+1)) hd4
    · have hqL : q 1 ≤ 13 := by have := hl 1; omega
      have hsum : totalP 6 p + totalQ 6 q ≤ 17 := by
        norm_num [totalP, totalQ, Fin.sum_univ_succ, hp1, hp3, hp5,
          hq0, hq2, hq3, hq4, hq5]
        omega
      rcases hd with ⟨_, hs⟩ | ⟨_, hs⟩ <;> omega
#print axioms Paper7C61Four.three_card_odd_q_one_impossible

end Paper7C61Four
