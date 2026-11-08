import Research.Backfill.Paper1.TightFamilies
import Research.Backfill.Paper1.PathLinearConvex

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral

theorem check_NearExampleDetails : NarrowSupplement.NearExampleDetails := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [NarrowPath.z_eq_Zp (by norm_num) 2 1 (by norm_num) (by norm_num)]
    norm_num [Zp, Wp, phiX, Challenge.g2, sum_Ico_succ_top]
  · rw [NarrowPath.z_eq_Zp (by norm_num) 2 0 (by norm_num) (by norm_num)]
    norm_num [Zp, Wp, phiX, sum_Ico_succ_top, sum_range_succ, Challenge.g2]
  · rw [NarrowPath.z_eq_Zp (by norm_num) 2 (-1) (by norm_num) (by norm_num)]
    norm_num [Zp, Wp, phiX, sum_Ico_succ_top, sum_range_succ, Challenge.g2]
  · ext i
    simp only [Challenge.NA, mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hi, he⟩
      rcases (show i = 0 ∨ i = 1 by omega) with h | h
      · exact h
      · subst i; norm_num [Challenge.g2] at he
    · rintro rfl
      norm_num [Challenge.g2]
  · rw [Additional.l1_tMulVec_eq_L1]
    exact TightFamilies.g2_three_data.1
  · intro p hp
    have hp2 : 2 < p := by linarith
    refine ⟨TightFamilies.first_G hp2, ?_⟩
    rw [PathAndSign.triple_eq_Mentry p 3 2 2 _ 2 2 le_rfl le_rfl,
      Mentry_prod p 3 2 2 (fun _ _ _ _ => rfl), TightFamilies.g2_three_data.2]
    change 0 < Tv p 2 sgnv 2 * 7
    exact mul_pos (Tv_sgnv_last_pos hp2 2) (by norm_num)

#print axioms check_NearExampleDetails
end CodexPaper1
