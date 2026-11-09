import Research.TaskE.C1Bounds

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma c1_high : CodexPaper1.TaskE.Challenge.C1HighThree := by
  intro a ha q hq g hg hna k y hy0 hy1 c hc hhigh
  have hy : 0 ≤ y ∧ y ≤ 1 := ⟨hy0, hy1⟩
  have hd := SProof.deficit_pos (a := a) (p := (3 : ℝ)) (by omega) (by norm_num) hg hna
  have hδ := delta_three_pos ha
  have hη := eta_times_q hq hy (n := k + 1) (by omega)
  have hterm := mul_pos hη.1 hd
  have hupper := mul_le_mul_of_nonneg_right hη.2 (show 0 ≤ 2 * deltaK a 3 by positivity)
  have hp := potential_lower a (by omega) q y hq hy0 hy1 c _ hc (chain_zeta_unit hq hg k)
  have hbase := mul_le_mul_of_nonneg_left hhigh (show 0 ≤ q - 1 by linarith)
  have hs := chain_sum_nonneg hq hy hg k
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c1_high
