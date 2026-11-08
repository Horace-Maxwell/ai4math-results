import Research.Backfill.Paper1.ThreeColumn
import Research.Backfill.Paper1.ColumnIdentity

/-! Full frozen Remark30. Both matrix families and the final closed formula
are included. Compilation and acceptance evidence is recorded separately. -/
set_option autoImplicit false
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace TightFamilies

lemma G_product_nonneg (a b : ℕ) (p q : ℝ) (e f : ℕ → ℝ)
    (he : 0 ≤ Tv p a e a) (hf : 0 ≤ Tv q b f b) :
    Challenge.Gval a b p q (fun i j => e i * f j) = L1 p a e * L1 q b f := by
  have hc : Challenge.triple a b p q (fun i j => e i * f j) a b =
      Tv p a e a * Tv q b f b := by
    rw [PathAndSign.triple_eq_Mentry p q a b _ a b le_rfl le_rfl]
    exact Mentry_prod p q a b (fun _ _ _ _ => rfl) a b
  rw [ColumnIdentity.Gval_corner, hc]
  have hn : Challenge.negPt (Tv p a e a * Tv q b f b) = 0 := by
    unfold Challenge.negPt
    exact max_eq_right (neg_nonpos.mpr (mul_nonneg he hf))
  rw [hn, mul_zero, sub_zero, PathAndSign.l1Mat_triple_eq_L1mat]
  exact L1mat_prod p q a b (fun _ _ _ _ => rfl)

lemma g2_three_data : L1 3 2 Challenge.g2 = 23 ∧ Tv 3 2 Challenge.g2 2 = 7 := by
  obtain ⟨h0, h1, h2⟩ := ThreeColumn.rows_two 3 Challenge.g2
  norm_num [ICGEqualParityB.Mc0, ICGEqualParityB.Mc1, ICGEqualParityB.Mc2,
    Challenge.g2] at h0 h1 h2
  constructor
  · rw [← Additional.l1_tMulVec_eq_L1]
    norm_num [Challenge.l1, Finset.sum_range_succ, h0, h1, h2]
  · rw [← Additional.tMulVec_eq_Tv 3 2 Challenge.g2 2 le_rfl]
    exact h2

lemma dNorm_two {p : ℝ} (hp : 2 < p) :
    Challenge.dNorm 2 p = 5 * p ^ 2 - 8 * p + 4 := by
  rw [ClosedForms.dNorm_eq_dClosed hp]
  norm_num [Challenge.dClosed, Finset.sum_range_succ]
  ring

lemma delta_two {p : ℝ} (hp : 2 < p) :
    Challenge.deltaK 2 p = p ^ 2 - 2 * p + 2 := by
  rw [ClosedForms.deltaK_eq_polynomial hp]
  norm_num [ClosedForms.altSum, Finset.sum_range_succ]
  ring

lemma first_G {p : ℝ} (hp : 2 < p) :
    Challenge.Gval 2 2 p 3 (fun i j => Challenge.sAlt i * Challenge.g2 j) =
      23 * Challenge.dNorm 2 p := by
  rw [G_product_nonneg 2 2 p 3 Challenge.sAlt Challenge.g2
    (Tv_sgnv_last_pos hp 2).le (by rw [g2_three_data.2]; norm_num),
    g2_three_data.1]
  change L1 p 2 sgnv * 23 = 23 * Challenge.dNorm 2 p
  rw [← Additional.dNorm_eq_L1]
  ring

lemma second_G {q : ℝ} (hq : 2 < q) (b : ℕ) :
    Challenge.Gval 2 b 3 q (fun i j => Challenge.g2 i * Challenge.sAlt j) =
      23 * Challenge.dNorm b q := by
  rw [G_product_nonneg 2 b 3 q Challenge.g2 Challenge.sAlt
    (by rw [g2_three_data.2]; norm_num) (Tv_sgnv_last_pos hq b).le,
    g2_three_data.1]
  change 23 * L1 q b sgnv = 23 * Challenge.dNorm b q
  rw [← Additional.dNorm_eq_L1]

end TightFamilies

theorem check_Remark30 : Challenge.Remark30 := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have hp2 : 2 < p := by linarith
    rw [TightFamilies.first_G hp2, Challenge.Theta,
      TightFamilies.dNorm_two hp2, TightFamilies.dNorm_two (by norm_num : (2 : ℝ) < 3),
      TightFamilies.delta_two hp2, TightFamilies.delta_two (by norm_num : (2 : ℝ) < 3)]
    ring
  · intro q hq b _hb _heven
    have hq2 : 2 < q := by linarith
    rw [TightFamilies.second_G hq2 b, Challenge.Theta,
      TightFamilies.dNorm_two (by norm_num : (2 : ℝ) < 3),
      TightFamilies.delta_two (by norm_num : (2 : ℝ) < 3)]
    ring
  · intro q hq
    have hq2 : 2 < q := by linarith
    rw [TightFamilies.dNorm_two hq2, TightFamilies.delta_two hq2]
    ring

#print axioms check_Remark30
end CodexPaper1
