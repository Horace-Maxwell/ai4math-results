import Research.Backfill.Paper1.SupplementStatements
import Research.Backfill.Paper1.Additional

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1
namespace NarrowCell

lemma neg (P μ A B : ℝ) : Challenge.hcell P μ (-A) (-B) = Challenge.hcell P μ A B :=
  ICGGeneral.hcell_neg P μ A B

lemma small {P μ A B : ℝ} (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A) :
    Challenge.hcell P μ A B = -2 * (P - μ) * B := by
  unfold Challenge.hcell
  rw [abs_of_nonneg hA, abs_of_nonneg hB,
    abs_of_nonneg (by linarith : 0 ≤ A - B),
    abs_of_nonneg (add_nonneg hB (mul_nonneg hP hA))]
  ring

lemma large {P μ A B : ℝ} (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A ≤ B) :
    Challenge.hcell P μ A B = 2 * (μ * B - P * A) := by
  unfold Challenge.hcell
  rw [abs_of_nonneg hA, abs_of_nonneg hB,
    abs_of_nonpos (by linarith : A - B ≤ 0),
    abs_of_nonneg (add_nonneg hB (mul_nonneg hP hA))]
  ring

lemma opp_small {P μ A B : ℝ} (_hP : 0 ≤ P) (hA : 0 ≤ A) (hB : B ≤ 0) (hBA : -B ≤ P * A) :
    Challenge.hcell P μ A B = 0 := by
  unfold Challenge.hcell
  rw [abs_of_nonneg hA, abs_of_nonpos hB,
    abs_of_nonneg (by linarith : 0 ≤ A - B),
    abs_of_nonneg (by linarith : 0 ≤ B + P * A)]
  ring

lemma opp_large {P μ A B : ℝ} (_hP : 0 ≤ P) (hA : 0 ≤ A) (hB : B ≤ 0) (hBA : P * A ≤ -B) :
    Challenge.hcell P μ A B = 2 * μ * (-B - P * A) := by
  unfold Challenge.hcell
  rw [abs_of_nonneg hA, abs_of_nonpos hB,
    abs_of_nonneg (by linarith : 0 ≤ A - B),
    abs_of_nonpos (by linarith : B + P * A ≤ 0)]
  ring

end NarrowCell

theorem check_CellValues : NarrowSupplement.CellValues := by
  intro P μ A B hP _hμ0 _hμ1
  have hP0 : 0 ≤ P := by linarith
  refine ⟨ICGGeneral.hcell_neg P μ A B, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Challenge.hcell, mul_zero, sub_zero, zero_sub, add_zero, abs_zero, abs_neg]
    ring
  · intro hAB hBA
    by_cases hA : 0 ≤ A
    · have hB : 0 ≤ B := by nlinarith
      simp only [abs_of_nonneg hA, abs_of_nonneg hB] at hBA ⊢
      exact NarrowCell.small hP0 hA hB hBA
    · have hA' : A ≤ 0 := by linarith
      have hB : B ≤ 0 := by nlinarith
      simp only [abs_of_nonpos hA', abs_of_nonpos hB] at hBA ⊢
      rw [← NarrowCell.neg P μ A B]
      exact NarrowCell.small hP0 (by linarith) (by linarith) hBA
  · intro hAB hBA
    by_cases hAz : A = 0
    · subst A
      have hB : B = 0 := by simpa using hBA
      subst B; norm_num [Challenge.hcell]
    by_cases hA : 0 ≤ A
    · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
      have hB : B ≤ 0 := by nlinarith
      rw [abs_of_nonneg hA, abs_of_nonpos hB] at hBA
      exact NarrowCell.opp_small hP0 hA hB hBA
    · have hAn : A < 0 := lt_of_not_ge hA
      have hB : 0 ≤ B := by nlinarith
      rw [abs_of_nonpos hAn.le, abs_of_nonneg hB] at hBA
      rw [← NarrowCell.neg P μ A B]
      apply NarrowCell.opp_small hP0 (by linarith) (by linarith)
      simpa using hBA
  · intro hAB hBA
    by_cases hA : 0 ≤ A
    · have hB : 0 ≤ B := by nlinarith
      simp only [abs_of_nonneg hA, abs_of_nonneg hB] at hBA ⊢
      exact NarrowCell.large hP0 hA hB hBA
    · have hA' : A ≤ 0 := by linarith
      have hB : B ≤ 0 := by nlinarith
      simp only [abs_of_nonpos hA', abs_of_nonpos hB] at hBA ⊢
      rw [← NarrowCell.neg P μ A B]
      exact NarrowCell.large hP0 (by linarith) (by linarith) hBA
  · intro hAB hBA
    by_cases hA : 0 < A
    · have hB : B ≤ 0 := by nlinarith
      rw [abs_of_nonneg hA.le, abs_of_nonpos hB] at hBA ⊢
      exact NarrowCell.opp_large hP0 hA.le hB hBA
    · by_cases hAz : A = 0
      · subst A
        norm_num [Challenge.hcell]
        ring
      · have hAn : A < 0 := lt_of_le_of_ne (le_of_not_gt hA) hAz
        have hB : 0 ≤ B := by nlinarith
        rw [abs_of_nonpos hAn.le, abs_of_nonneg hB] at hBA ⊢
        rw [← NarrowCell.neg P μ A B]
        simpa using NarrowCell.opp_large hP0 (by linarith : 0 ≤ -A)
          (by linarith : -B ≤ 0) (by simpa using hBA)

theorem check_CellStrictBoundary : NarrowSupplement.CellStrictBoundary := by
  constructor
  · intro P μ A B hP hμ0 hμ1 hAB hBA
    have h := check_CellValues P μ A B hP hμ0 hμ1
    have hB : 0 < |B| := abs_pos.mpr (by intro hz; rw [hz, mul_zero] at hAB; linarith)
    rcases le_total |B| |A| with hsmall | hlarge
    · rw [h.2.2.1 hAB hsmall]
      have hPm : 0 < P - μ := by linarith
      nlinarith [mul_pos hPm hB]
    · rw [h.2.2.2.2.1 hAB hlarge]
      have hm := mul_le_mul_of_nonneg_right hμ1 hB.le
      nlinarith
  · intro P μ A hP hμ hμ1 hA
    have hP0 : 0 < P := by linarith
    have hB : 0 < P * A / μ := div_pos (mul_pos hP0 hA) hμ
    have hAB : 0 < A * (P * A / μ) := mul_pos hA hB
    have hlarge : |A| ≤ |P * A / μ| := by
      rw [abs_of_pos hA, abs_of_pos hB]
      apply (le_div_iff₀ hμ).mpr
      nlinarith
    rw [(check_CellValues P μ A (P * A / μ) hP hμ.le hμ1).2.2.2.2.1 hAB hlarge,
      abs_of_pos hA, abs_of_pos hB]
    field_simp
    ring

#print axioms check_CellValues
#print axioms check_CellStrictBoundary
end CodexPaper1
