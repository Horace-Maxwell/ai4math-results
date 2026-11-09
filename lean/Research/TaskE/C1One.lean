import Research.TaskE.C1Bounds

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma c1_one_nonalt : CodexPaper1.TaskE.Challenge.C1OneNonaltThree := by
  intro a ha q hq g hg hna y hy0 hy1 c hc hcna
  have hy : 0 ≤ y ∧ y ≤ 1 := ⟨hy0, hy1⟩
  have hdg := deficit_lower a ha g hg hna
  have hdc := deficit_lower a ha c hc hcna
  have hδ := two_delta_upper ha
  have hgp := SProof.deficit_pos (a := a) (p := (3 : ℝ)) (by omega) (by norm_num) hg hna
  have hcp := SProof.deficit_pos (a := a) (p := (3 : ℝ)) (by omega) (by norm_num) hc hcna
  have hm := q_parameters hq
  have he := q_mu_one hq
  have hlo := mu_zero_lower hq
  have hq0 : 0 < q := by linarith
  have hV : 0 < q * mu q 1 := by
    exact mul_pos hq0 (hm.1.trans_le (hm.2.1.trans hm.2.2.1))
  have hA : 0 ≤ (q - 1) * (1 + mu q 0) + q * mu q 1 := by
    have hP : 0 ≤ q - 1 := by linarith
    have hu0 : 0 ≤ mu q 0 := hm.1.le
    positivity
  have hmulG := mul_le_mul_of_nonneg_left hdg hA
  have hmulC := mul_le_mul_of_nonneg_left hdc (show 0 ≤ q - 1 by linarith)
  have hmulδ := mul_le_mul_of_nonneg_left hδ hV.le
  have hcoef : 0 < (8 / 27 : ℝ) *
      ((q - 1) * (1 + mu q 0) + q * mu q 1 + (q - 1)) -
      q * mu q 1 * (28 / 27 : ℝ) := by
    have hz := mul_nonneg (show 0 ≤ q - 1 by linarith) (show 0 ≤ mu q 0 - 3 / 5 by linarith)
    nlinarith
  have hpos := mul_pos hcoef (show 0 < (3 : ℝ) ^ a by positivity)
  have hscalar : q * mu q 1 * (2 * deltaK a 3 - DeltaC a 3 g) <
      (q - 1) * (1 + mu q 0) * DeltaC a 3 g + (q - 1) * DeltaC a 3 c := by
    nlinarith
  have hη1 := eta_lower_mu hq hy (n := 1) (by omega)
  have hη2 := eta_upper_mu hq hy (n := 2) (by omega)
  have hη0 := (eta_unit hq hy 2).1
  have hchain := mul_le_mul_of_nonneg_right hη1
    (mul_nonneg (by linarith : 0 ≤ q - 1) hgp.le)
  have hζ : ∀ i ≤ a, |-mu q 0 * g i| ≤ 1 := by
    have hh := chain_zeta_unit hq hg 1
    simpa using hh
  have hp := potential_lower a (by omega) q y hq hy0 hy1 c _ hc hζ
  by_cases hγ : 0 ≤ 2 * deltaK a 3 - DeltaC a 3 g
  · have hr := mul_le_mul_of_nonneg_left hη2
      (mul_nonneg hq0.le hγ)
    nlinarith
  · have hr : q * etaMap q 2 y * (2 * deltaK a 3 - DeltaC a 3 g) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hq0.le hη0) (by linarith)
    have hbas : 0 < (q - 1) * DeltaC a 3 c := mul_pos (by linarith) hcp
    have hchain0 : 0 ≤ (q - 1) * (1 + etaMap q 1 y) * DeltaC a 3 g := by
      have h1 := (eta_unit hq hy 1).1
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hgp.le
    linarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c1_one_nonalt
