import Research.TaskE.C1Bounds

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma c1_long : CodexPaper1.TaskE.Challenge.C1LongThree := by
  intro a ha q hq g hg hna k hk y hy0 hy1 c hc
  have hy : 0 ≤ y ∧ y ≤ 1 := ⟨hy0, hy1⟩
  have hd := SProof.deficit_pos (a := a) (p := (3 : ℝ)) (by omega) (by norm_num) hg hna
  have hγ := gamma_upper ha hg hna
  have hs := chain_sum_two hq hy hg hk
  have hu := eta_upper_mu hq hy (n := k + 1) (by omega)
  have hη := (eta_unit hq hy (k + 1)).1
  have hm := q_parameters hq
  have he := q_mu_one hq
  have hlo := mu_zero_lower hq
  have hq0 : 0 < q := by linarith
  have hr : q * etaMap q (k + 1) y * (2 * deltaK a 3 - DeltaC a 3 g) ≤
      q * mu q 1 * ((5 / 2 : ℝ) * DeltaC a 3 g) := by
    calc
      _ ≤ q * etaMap q (k + 1) y * ((5 / 2 : ℝ) * DeltaC a 3 g) :=
        mul_le_mul_of_nonneg_left hγ (mul_nonneg hq0.le hη)
      _ ≤ _ := by
        have ht := mul_le_mul_of_nonneg_left hu
          (show 0 ≤ q * ((5 / 2 : ℝ) * DeltaC a 3 g) by positivity)
        nlinarith
  have hcoef : 0 < 2 * ((q - 1) * (1 + mu q 0)) - q * mu q 1 * (5 / 2 : ℝ) := by
    have hz := mul_nonneg (show 0 ≤ q - 1 by linarith) (show 0 ≤ mu q 0 - 3 / 5 by linarith)
    nlinarith
  have hstrict := mul_pos hcoef hd
  have hp := potential_lower a (by omega) q y hq hy0 hy1 c _ hc (chain_zeta_unit hq hg k)
  have hdc := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hc
  have hpot : 0 ≤ psi a 3 q y c (fun i => (-1) ^ k * mu q ((k : ℤ) - 1) * g i) := by
    exact (mul_nonneg (by linarith) hdc).trans hp
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.c1_long
