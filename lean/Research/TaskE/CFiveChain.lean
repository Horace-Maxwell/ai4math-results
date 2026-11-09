import Research.TaskE.DeficitLower
import Research.TaskE.FCParameters

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma five_chain : CodexPaper1.TaskE.Challenge.FiveChainThree := by
  intro a ha q hq g hg hna y hy
  have hd := deficit_lower a ha g hg hna
  have hdp : 0 < DeltaC a 3 g := SProof.deficit_pos (by omega) (by norm_num) hg hna
  have hδ := two_delta_upper ha
  have hγ : 2 * deltaK a 3 - DeltaC a 3 g ≤ (5 / 2 : ℝ) * DeltaC a 3 g := by
    nlinarith
  have hi := initial_unit hq hy
  have hη := eta_unit hq hi 5
  have hq0 : 0 < q := by linarith
  have hP : 0 ≤ q - 1 := by linarith
  have hs : 5 * ((q - 1) * DeltaC a 3 g) ≤
      ∑ n ∈ range 5, (q - 1) * (1 + etaMap q n y) * DeltaC a 3 g := by
    calc
      _ = ∑ _n ∈ range 5, (q - 1) * DeltaC a 3 g := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro n _hn
        have hηn := (eta_unit hq hi n).1
        nlinarith [mul_nonneg hηn (mul_nonneg hP hdp.le)]
  have hr : q * etaMap q 5 y * (2 * deltaK a 3 - DeltaC a 3 g) ≤
      q * ((5 / 2 : ℝ) * DeltaC a 3 g) := by
    calc
      _ ≤ q * etaMap q 5 y * ((5 / 2 : ℝ) * DeltaC a 3 g) :=
        mul_le_mul_of_nonneg_left hγ (mul_nonneg hq0.le hη.1)
      _ ≤ _ := by
        have hnon : 0 ≤ q * ((5 / 2 : ℝ) * DeltaC a 3 g) := by positivity
        have hx := mul_le_mul_of_nonneg_right hη.2 hnon
        nlinarith
  have hm := mul_pos (by linarith : 0 < 5 * (q - 1) - (5 / 2 : ℝ) * q) hdp
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.five_chain
