import Research.TaskE.ChallengeF
import Research.TaskE.FCParameters

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open BackfillPaper1.Challenge

lemma delta_ratio : CodexPaper1.TaskE.Challenge.DeltaRatioThree := by
  intro a ha
  have hw : (3 : ℝ) ^ a = 3 ^ (a - 1) * 3 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ a)]
  have he := two_delta_three a
  rcases Nat.even_or_odd a with hev | hod
  · have ha4 : 4 ≤ a := by
      have hm := Nat.even_iff.mp hev
      omega
    have hp : (81 : ℝ) ≤ 3 ^ a := by
      calc
        (81 : ℝ) = 3 ^ (4 : ℕ) := by norm_num
        _ ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) ha4
    rw [hev.neg_one_pow] at he
    nlinarith
  · rw [hod.neg_one_pow] at he
    have hp : 0 < (3 : ℝ) ^ a := by positivity
    nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.delta_ratio
