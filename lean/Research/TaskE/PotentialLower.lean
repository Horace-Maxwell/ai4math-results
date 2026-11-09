import Research.TaskE.ChallengeFC
import Research.TaskE.SUniform
import Research.Backfill.Paper1.Prop31Base

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma potential_lower : CodexPaper1.TaskE.Challenge.PotentialLowerThree := by
  intro a ha q μ hq hμ0 hμ1 c ζ hc hζ
  let B := ∑ i ∈ range (a + 1),
    max 0 (|tMulVec a 3 ζ i| - (q - 1) * |tMulVec a 3 c i|)
  have hlast := SProof.terminal_penalty_zero (p := 3) (K := q - 1) ha
    (by norm_num) (by linarith) (by linarith) hc
  have hB : B ≤ 2 * DeltaC a 3 c := by
    calc
      B ≤ ∑ i ∈ range (a + 1),
          max 0 (rowAbsSum a 3 i - (q - 1) * |tMulVec a 3 c i|) := by
        apply sum_le_sum
        intro i _hi
        apply max_le_max le_rfl
        linarith [CodexPaper1.Prop31.tMulVec_abs_le_rowAbs a 3 ζ hζ i]
      _ = ∑ i ∈ range a,
          max 0 (rowAbsSum a 3 i - (q - 1) * |tMulVec a 3 c i|) := by
        rw [sum_range_succ, hlast, add_zero]
      _ ≤ ∑ i ∈ range a, max 0 (rowAbsSum a 3 i - 2 * |tMulVec a 3 c i|) := by
        apply sum_le_sum
        intro i _hi
        apply max_le_max le_rfl
        nlinarith [abs_nonneg (tMulVec a 3 c i)]
      _ ≤ _ := SProof.penalty_bound a ha 3 (by norm_num) c hc
  have hh : (∑ i ∈ range (a + 1), hcell (q - 1) μ
      (tMulVec a 3 c i) (tMulVec a 3 ζ i)) ≤ 2 * μ * B := by
    rw [show 2 * μ * B = ∑ i ∈ range (a + 1),
      2 * μ * max 0 (|tMulVec a 3 ζ i| - (q - 1) * |tMulVec a 3 c i|) by
        dsimp [B]; rw [mul_sum]]
    apply sum_le_sum
    intro i _hi
    exact ICGGeneral.hcell_le hμ0 hμ1 (by linarith) _ _
  have hD : 0 ≤ DeltaC a 3 c := CodexPaper1.Prop31.delta_nonneg (by norm_num) hc
  have h4 := mul_nonneg (by linarith : 0 ≤ q - 1 - 4) (mul_nonneg hμ0 hD)
  have hmult := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2 * μ by positivity)
  unfold psi
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.potential_lower
