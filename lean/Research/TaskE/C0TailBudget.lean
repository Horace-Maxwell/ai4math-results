import Research.TaskE.C0BudgetBasis

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma zero_tail_budget : CodexPaper1.TaskE.Challenge.ZeroTailBudgetThree := by
  intro a ha g hg j hj
  have hb := potential_tail_budget hg (a - (j + 1)) (j + 1) (by omega)
  rw [potential_tail_sum hj,
    ← CodexPaper1.Additional.mu_nat_eq_nu 3 j,
    ← CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a g j hj] at hb
  have hm := SProof.mu_lower (p := (3 : ℝ)) (by norm_num) j
  have hv := (SProof.path_bounds ha hj (by norm_num : (3 : ℝ) ≤ 3) hg).2.2
  norm_num at hm
  have hmul := mul_nonneg (show 0 ≤ mu 3 (j : ℤ) - 1 / 3 by linarith)
    (show 0 ≤ 1 - |z 3 a g (j : ℤ)| by linarith)
  have hp := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * (3 : ℝ) ^ a by positivity)
  have hweighted := CodexPaper1.ClosedForms.weighted_nu_eq_deltaK (x := (3 : ℝ)) (by norm_num) a
  have hscale := length_scale ha
  have he := mul_nonneg (show 0 ≤ 2 * (3 : ℝ) ^ a by positivity) hmul
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.zero_tail_budget
