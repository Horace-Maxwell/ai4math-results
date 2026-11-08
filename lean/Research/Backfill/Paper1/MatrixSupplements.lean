import Research.Backfill.Paper1.GeneralEqualityBase
import Research.Backfill.Paper1.TransformRows

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace NarrowMatrix

lemma row_early {p : ℝ} (hp : 2 < p) {a i : ℕ} (ha : 1 ≤ a) (hi : i < a) :
    Challenge.rowAbsSum a p i = 2 * p ^ (a - 1) * (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  let c : ℝ := p ^ (a - 1) * (p - 1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hentry (j : ℕ) (hj : j ∈ range (a + 1)) :
      |Challenge.tEntry a p i j| = Challenge.tEntry a p i j +
        if j = a - 1 - i then 2 * c else 0 := by
    have hjle : j ≤ a := by simpa using mem_range.mp hj
    by_cases he : j = a - 1 - i
    · subst j
      have hn : a - 1 - i < a := by omega
      have heq : i + (a - 1 - i) + 1 = a := by omega
      simp only [Challenge.tEntry, hi, hn, and_self, ite_true, heq,
        show ¬ i + (a - 1 - i) + 2 ≤ a by omega, ite_false]
      change |-c| = -c + 2 * c
      rw [abs_neg, abs_of_nonneg hc]
      ring
    · have hn : 0 ≤ Challenge.tEntry a p i j := by
        unfold Challenge.tEntry
        split_ifs <;> first | positivity | (exfalso; apply he; omega)
      rw [abs_of_nonneg hn, ite_eq_right he, add_zero]
  have hsum : (∑ j ∈ range (a + 1), Challenge.tEntry a p i j) = 0 := by
    have h := (check_TransformRows p (by linarith) a ha).2 i hi.le
    simpa [Challenge.tMulVec, hi.ne] using h
  unfold Challenge.rowAbsSum
  rw [sum_congr rfl hentry, sum_add_distrib, hsum]
  simp only [sum_ite_eq', mem_range, show a - 1 - i < a + 1 by omega, ite_true, zero_add]
  dsimp [c]
  ring

lemma row_last {p : ℝ} (hp : 2 < p) {a : ℕ} (ha : 1 ≤ a) :
    Challenge.rowAbsSum a p a = p ^ a := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have he (j : ℕ) (_hj : j ∈ range (a + 1)) :
      |Challenge.tEntry a p a j| = Challenge.tEntry a p a j := by
    apply abs_of_nonneg
    simp only [Challenge.tEntry, lt_self_iff_false, false_and, ite_false]
    split_ifs <;> positivity
  unfold Challenge.rowAbsSum
  rw [sum_congr rfl he]
  have h := (check_TransformRows p (by linarith) a ha).2 a le_rfl
  simpa [Challenge.tMulVec] using h

lemma abs_row_bound (a : ℕ) (p : ℝ) (ζ : ℕ → ℝ)
    (hζ : ∀ i ≤ a, |ζ i| ≤ 1) (i : ℕ) :
    |Challenge.tMulVec a p ζ i| ≤ Challenge.rowAbsSum a p i := by
  unfold Challenge.tMulVec Challenge.rowAbsSum
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro j hj
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_left (hζ j (by simpa using mem_range.mp hj))
    (abs_nonneg (Challenge.tEntry a p i j))

end NarrowMatrix

theorem check_MatrixFacts : NarrowSupplement.MatrixFacts := by
  intro p hp a ha
  refine ⟨?_, by simp [Challenge.tEntry], NarrowMatrix.row_last hp (by omega), ?_⟩
  · intro i hi
    refine ⟨?_, NarrowMatrix.row_early hp (by omega) hi, ?_⟩
    · simpa only [GeneralEquality.unitColumn, show a - i - 1 = a - 1 - i by omega]
        using GeneralEquality.unitColumn_early hi p
    · have h := GeneralEquality.alpha_row hp hi
      rw [← Additional.mu_pred_eq_nu] at h
      exact h
  · intro j hj
    simp only [Challenge.tEntry, lt_self_iff_false, false_and, ite_false, hj, ite_true]
    rw [show a - j - 1 = a - 1 - j by omega]

theorem check_MatrixBounds : NarrowSupplement.MatrixBounds := by
  intro a ha p q hreg
  have hp := (OneColumn.region_bounds hreg).1
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hs := GeneralEquality.region_strict hreg ha
  refine ⟨?_, ?_, GeneralEquality.delta_lower hp (by omega), hs.2.2.2.1, hs.2.2.2.2, ?_⟩
  · intro ζ hζ i _hi
    exact NarrowMatrix.abs_row_bound a p ζ hζ i
  · intro i hi
    exact (GeneralEquality.unit_le_half_alpha hreg ha hi.le).2
  · intro i hi
    by_cases he : i = a
    · subst i
      rw [NarrowMatrix.row_last hp (by omega)]
      change p ^ a ≤ (q - 1) * |GeneralEquality.alpha a p a|
      rw [GeneralEquality.alpha_last hp, abs_of_nonneg (by linarith [hs.2.2.2.1])]
      exact hs.2.2.2.2.le
    · have hit : i < a := lt_of_le_of_ne hi he
      rw [NarrowMatrix.row_early hp (by omega) hit]
      change 2 * p ^ (a - 1) * (p - 1) ≤ (q - 1) * |GeneralEquality.alpha a p i|
      rw [GeneralEquality.alpha_row_abs hp hit]
      have hn := nu_pos hp i
      have hw : 0 ≤ p ^ (a - 1) * (p - 1) := by positivity
      have hf : 2 ≤ (q - 1) * (1 + nu p i) := by nlinarith [hs.2.2.1]
      nlinarith [mul_le_mul_of_nonneg_left hf hw]

#print axioms check_MatrixFacts
#print axioms check_MatrixBounds
end CodexPaper1
