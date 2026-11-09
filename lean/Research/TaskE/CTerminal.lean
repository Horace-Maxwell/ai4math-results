import Research.TaskE.DeficitLower
import Research.TaskE.FCParameters

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma terminal_ratios : CodexPaper1.TaskE.Challenge.TerminalRatiosThree := by
  intro a ha q hq g hg hna
  have hd := deficit_lower a ha g hg hna
  have hdp : 0 < DeltaC a 3 g := SProof.deficit_pos (by omega) (by norm_num) hg hna
  have hδ := two_delta_upper ha
  have htw : 2 * deltaK a 3 < 4 * DeltaC a 3 g := by nlinarith
  obtain ⟨hm0, h0L, hL1, hm1⟩ := q_parameters hq
  have hq0 : 0 < q := by linarith
  have hL0 : 0 < muInf q := hm0.trans_le h0L
  have hm1p : 0 < mu q 1 := hL0.trans_le hL1
  have hLle : muInf q ≤ 1 := hL1.trans hm1
  have hD1 : 2 ≤ Dhat1 q := by
    unfold Dhat1
    rw [le_div_iff₀ hq0]
    linarith
  have hr1 : 2 ≤ Dhat1 q / mu q 1 := by
    rw [le_div_iff₀ hm1p]
    linarith
  have hD2 : 2 ≤ Dhat2 q := by
    unfold Dhat2
    rw [le_div_iff₀ (sq_pos_of_pos hq0)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ q - 5) hq0.le]
  have hr2 : 2 ≤ Dhat2 q / muInf q := by
    rw [le_div_iff₀ hL0]
    linarith
  split_ifs with he
  · have hm := mul_le_mul_of_nonneg_left hr1 hdp.le
    nlinarith
  · have ho : Odd a := Nat.not_even_iff_odd.mp he
    have hodd := deficit_odd_lower (by omega) ho hg hna
    have hdelt := two_delta_three a
    rw [ho.neg_one_pow] at hdelt
    have hmu0 := (CodexPaper1.check_MuBounds q (by linarith)).2.2.1
    have hD10 : 3 * mu q 0 < Dhat1 q := by
      rw [hmu0]
      unfold Dhat1
      field_simp
      linarith
    have hratio : 3 < Dhat1 q / mu q 0 := by
      rw [lt_div_iff₀ hm0]
      exact hD10
    constructor
    · have hm := mul_lt_mul_of_pos_left hratio hdp
      have heq : DeltaC a 3 g * Dhat1 q / mu q 0 =
          DeltaC a 3 g * (Dhat1 q / mu q 0) := by ring
      rw [heq]
      nlinarith
    · have hm := mul_le_mul_of_nonneg_left hr2 hdp.le
      nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.terminal_ratios
