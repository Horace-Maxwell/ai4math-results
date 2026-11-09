import Research.TaskE.PotentialLower
import Research.TaskE.FCParameters

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma high_deficit_F : CodexPaper1.TaskE.Challenge.HighDeficitFThree := by
  intro a ha q hq c hc hd t ht
  obtain ⟨hu, hm, hr⟩ := family_bounds hq ht
  have hζ : ∀ i ≤ a, |t.2.1 * sAlt i| ≤ 1 := by
    intro i _hi
    have hs : |sAlt i| = 1 := by simp [sAlt, abs_pow]
    rw [abs_mul, abs_of_nonneg hm.1, hs, mul_one]
    exact hm.2
  have hp := potential_lower a (by omega) q t.1 hq hu.1 hu.2 c _ hc hζ
  have hδ := delta_three_pos ha
  have hbase := mul_le_mul_of_nonneg_left hd (show 0 ≤ q - 1 by linarith)
  have hstrict := mul_lt_mul_of_pos_right hr (show 0 < 2 * deltaK a 3 by positivity)
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.high_deficit_F
