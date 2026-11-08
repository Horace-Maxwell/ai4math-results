import Research.Backfill.Paper1.GeneralEqualityBase

/-!
Complete frozen Lemma24: the second extremal matrix in arbitrary dimension,
including its defect, every zero column surplus, positive final coordinate,
G = Theta, and the converse uniqueness statement. Acceptance is recorded by
check_generalequality.py separately; this source header makes no acceptance claim.
-/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral
namespace GeneralEquality

lemma plus_base_dot {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) (hab : Even (a + b)) {i : ℕ} (hi : i ≤ a) :
    0 ≤ (sgnv b * alpha a p i) * state a b p q (Challenge.Yplus a b) i b := by
  have heq := Chain.tMulVec_scale_of_eq a p 1
    (Challenge.col (Challenge.Yplus a b) b) (Challenge.gPlus a)
    (by intro t ht; simpa only [one_mul, Challenge.col] using col_plus_last hab t ht) i
  rw [state_last, heq, one_mul, tMul_gPlus, even_sum_sign hab]
  apply dot_base_nonneg (unit_le_half_alpha hreg ha hi).1
  rw [abs_mul, sign_abs, one_mul]
  exact (unit_le_half_alpha hreg ha hi).2

lemma plus_cell_zero {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) (hab : Even (a + b)) {j : ℕ} (hj : j < b) {i : ℕ} (hi : i ≤ a) :
    Challenge.hcell (q - 1) (Challenge.mu q ((j : ℤ) - 1))
      (Challenge.tMulVec a p (Challenge.col (Challenge.Yplus a b) j) i)
      (Challenge.tMulVec a p (Challenge.zetaPath b q (Challenge.Yplus a b) j) i) = 0 := by
  have hq : q ≠ 0 := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have hY := plus_sign hab
  rw [← state_succ_zeta hq a b p (Challenge.Yplus a b) i j hj,
    Chain.tMulVec_scale_of_eq a p _ _ Challenge.sAlt (col_plus_early hj) i]
  change Challenge.hcell (q - 1) (Challenge.mu q ((j : ℤ) - 1))
    (sgnv j * alpha a p i) (state a b p q (Challenge.Yplus a b) i (j + 1)) = 0
  apply cell_zero_of_dot
  · have hn : 0 ≤ (sgnv (j + 1) * alpha a p i) *
        state a b p q (Challenge.Yplus a b) i (j + 1) := by
      by_cases he : j + 1 = b
      · rw [he]
        exact plus_base_dot hreg ha hab hi
      · exact state_column_dot hreg hY hi (by omega) (col_plus_early (by omega))
    rw [sgnv_succ] at hn
    nlinarith
  · rw [abs_mul, sign_abs, one_mul]
    exact state_bound hreg hY hi hj

lemma plus_psi_zero {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) (hab : Even (a + b)) {j : ℕ} (hj : j < b) :
    Challenge.psiCol a b p q (Challenge.Yplus a b) j = 0 := by
  have hc : Challenge.IsPmAlt a (Challenge.col (Challenge.Yplus a b) j) := by
    rcases sgnv_isSign j j le_rfl with hs | hs
    · left; intro i hi; simpa only [hs, one_mul] using col_plus_early hj i hi
    · right; intro i hi; simpa only [hs, neg_one_mul] using col_plus_early hj i hi
  unfold Challenge.psiCol Challenge.psi
  rw [OneColumn.delta_pmAlt hc, mul_zero]
  have hz : (∑ i ∈ range (a + 1),
      Challenge.hcell (q - 1) (Challenge.mu q ((j : ℤ) - 1))
        (Challenge.tMulVec a p (Challenge.col (Challenge.Yplus a b) j) i)
        (Challenge.tMulVec a p (Challenge.zetaPath b q (Challenge.Yplus a b) j) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact plus_cell_zero hreg ha hab hj (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  rw [hz, sub_zero]

lemma plus_final_positive {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : Even (a + b)) :
    0 < Challenge.tMulVec a p (Challenge.zetaPath b q (Challenge.Yplus a b) (-1)) a := by
  have hq : q ≠ 0 := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have h := state_last_step_pos hreg ha (plus_sign hab) (show 0 < b by omega)
    (col_plus_early (show 0 < b by omega))
  rw [sgnv_zero, one_mul, state_eq_zeta hq a b p (Challenge.Yplus a b) a 0 (Nat.zero_le b)] at h
  simpa only [Int.natCast_zero, zero_sub] using h

lemma plus_value {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hab : Even (a + b)) :
    Challenge.Gval a b p q (Challenge.Yplus a b) = Challenge.Theta a b p q := by
  obtain ⟨hp, hq, _, _, _⟩ := region_strict hreg ha
  have h := ColumnIdentity.identity hq a b p (Challenge.Yplus a b)
  have hsum : (∑ j ∈ range b, Challenge.psiCol a b p q (Challenge.Yplus a b) j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact plus_psi_zero hreg ha hab (Finset.mem_range.mp hj)
  have hdelta : Challenge.DeltaC a p (Challenge.col (Challenge.Yplus a b) b) =
      Challenge.DeltaC a p (Challenge.gPlus a) := by
    apply Chain.delta_sign_scale a p 0 _ _
    intro i hi
    simpa only [pow_zero, one_mul, Challenge.col] using col_plus_last hab i hi
  have hneg : Challenge.negPt
      (Challenge.tMulVec a p (Challenge.zetaPath b q (Challenge.Yplus a b) (-1)) a) = 0 := by
    unfold Challenge.negPt
    rw [max_eq_right (by have := plus_final_positive hreg ha hb hab; linarith)]
  rw [hsum, hdelta, delta_gPlus (by omega) hp, sub_self, hneg] at h
  simp only [mul_zero, add_zero] at h
  have hn : q ^ (1 - (b : ℤ)) ≠ 0 := zpow_ne_zero _ (by linarith : q ≠ 0)
  have he := (mul_eq_zero.mp h).resolve_left hn
  linarith

lemma last_cell_zero {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y)
    {j : ℕ} (hj : j < b) (hc : Challenge.IsPmAlt a (Challenge.col Y j))
    (hpsi : Challenge.psiCol a b p q Y j = 0) :
    Challenge.hcell (q - 1) (Challenge.mu q ((j : ℤ) - 1))
      (Challenge.tMulVec a p (Challenge.col Y j) a) (state a b p q Y a (j + 1)) = 0 := by
  have hq : 2 < q := by have := (OneColumn.region_bounds hreg).2.1; linarith
  have hmu0 : 0 ≤ Challenge.mu q ((j : ℤ) - 1) := by
    rw [Additional.mu_pred_eq_nu]
    exact (nu_pos hq j).le
  have hmu1 : Challenge.mu q ((j : ℤ) - 1) ≤ 1 := by
    rw [Additional.mu_pred_eq_nu]
    exact (nu_bounds hq.le j).2
  have hz : ∀ i ≤ a, |Challenge.zetaPath b q Y j i| ≤ 1 := by
    have h := zeta_bound (by linarith : 1 ≤ q) hY (show j + 1 ≤ b by omega)
    rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega] at h
    exact h
  have H := (check_Lemma22 a ha p q hreg (Challenge.mu q ((j : ℤ) - 1)) hmu0 hmu1
    (Challenge.col Y j) (Challenge.zetaPath b q Y j)
    (fun i hi => hY i hi j hj.le) hz).2 hc
  have hcell := H.2.2.mp hpsi a le_rfl
  rw [state_succ_zeta (by linarith : q ≠ 0) a b p Y a j hj]
  exact hcell

lemma column_forced {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) {Y : ℕ → ℕ → ℝ} (hY : Challenge.IsSignMat a b Y)
    {j : ℕ} (hj : j < b) (hc : Challenge.IsPmAlt a (Challenge.col Y j))
    (hpsi : Challenge.psiCol a b p q Y j = 0)
    (hinv : 0 < sgnv (j + 1) * state a b p q Y a (j + 1)) :
    ∀ i ≤ a, Challenge.col Y j i = sgnv j * Challenge.sAlt i := by
  obtain ⟨hp, hq, hP, hd, hstrict⟩ := region_strict hreg ha
  have hm0 : 0 ≤ Challenge.mu q ((j : ℤ) - 1) := by
    rw [Additional.mu_pred_eq_nu]; exact (nu_pos hq j).le
  have hm1 : Challenge.mu q ((j : ℤ) - 1) ≤ 1 := by
    rw [Additional.mu_pred_eq_nu]; exact (nu_bounds hq.le j).2
  have hB : |state a b p q Y a (j + 1)| < (q - 1) * Challenge.deltaK a p :=
    lt_of_le_of_lt (state_last_bound hreg hY hj) hstrict
  have hzero := last_cell_zero hreg ha hY hj hc hpsi
  rcases hc with hc | hc
  · have hA : Challenge.tMulVec a p (Challenge.col Y j) a = Challenge.deltaK a p := by
      have h := Chain.tMulVec_scale_of_eq a p 1 (Challenge.col Y j) Challenge.sAlt
        (by intro i hi; simpa only [one_mul] using hc i hi) a
      rw [one_mul] at h
      exact h.trans (alpha_last hp a)
    rw [hA] at hzero
    have hZ := ICGEqualParityB.hc_zero_imp hm0 hm1 (by linarith) (by linarith) hB hzero
    have hs : sgnv j = 1 := by
      rcases sgnv_isSign j j le_rfl with hs | hs
      · exact hs
      · rw [sgnv_succ, hs] at hinv
        norm_num at hinv
        linarith
    intro i hi
    rw [hc i hi, hs, one_mul]
  · have hA : Challenge.tMulVec a p (Challenge.col Y j) a = -Challenge.deltaK a p := by
      have h := Chain.tMulVec_scale_of_eq a p (-1) (Challenge.col Y j) Challenge.sAlt
        (by intro i hi; simpa only [neg_one_mul] using hc i hi) a
      rw [neg_one_mul, show Challenge.tMulVec a p Challenge.sAlt a = Challenge.deltaK a p from alpha_last hp a] at h
      exact h
    rw [hA] at hzero
    have hZ := ICGEqualParityB.hc_zero_imp' hm0 hm1 (by linarith) (by linarith)
      (by simpa only [neg_neg] using hB) hzero
    have hs : sgnv j = -1 := by
      rcases sgnv_isSign j j le_rfl with hs | hs
      · rw [sgnv_succ, hs] at hinv
        norm_num at hinv
        linarith
      · exact hs
    intro i hi
    rw [hc i hi, hs, neg_one_mul]

lemma uniqueness {p q : ℝ} (hreg : Challenge.Regions p q) {a b : ℕ}
    (ha : 2 ≤ a) (hab : Even (a + b)) {Y : ℕ → ℕ → ℝ}
    (hY : Challenge.IsSignMat a b Y) (hLast : ∀ i ≤ a, Y i b = Challenge.gPlus a i)
    (hCols : ∀ j < b, Challenge.IsPmAlt a (Challenge.col Y j) ∧
      Challenge.psiCol a b p q Y j = 0) :
    Challenge.MatEq a b Y (Challenge.Yplus a b) := by
  obtain ⟨hp, _hq, _hP, hd, _hstrict⟩ := region_strict hreg ha
  have hbase : 0 < sgnv b * state a b p q Y a b := by
    have h := Chain.tMulVec_scale_of_eq a p 1 (Challenge.col Y b) (Challenge.gPlus a)
      (by intro i hi; simpa only [one_mul, Challenge.col] using hLast i hi) a
    rw [state_last, h, one_mul, tMul_gPlus, alpha_last hp, unitColumn_last, even_sum_sign hab]
    rcases sgnv_isSign b b le_rfl with hs | hs <;> rw [hs] <;> nlinarith
  have hinv : ∀ d, d ≤ b → 0 < sgnv (b - d) * state a b p q Y a (b - d) := by
    intro d
    induction d with
    | zero => intro _; simpa only [Nat.sub_zero] using hbase
    | succ d ih =>
      intro hd
      have hj : b - (d + 1) < b := by omega
      have hnext : b - (d + 1) + 1 = b - d := by omega
      have hc := column_forced hreg ha hY hj (hCols _ hj).1 (hCols _ hj).2
        (by rw [hnext]; exact ih (by omega))
      exact state_last_step_pos hreg ha hY hj hc
  intro i hi j hj
  by_cases he : j = b
  · subst j
    exact (hLast i hi).trans (col_plus_last hab i hi).symm
  · have hjt : j < b := lt_of_le_of_ne hj he
    have hs : 0 < sgnv (j + 1) * state a b p q Y a (j + 1) := by
      have h := hinv (b - (j + 1)) (Nat.sub_le _ _)
      rwa [show b - (b - (j + 1)) = j + 1 by omega] at h
    have hc := column_forced hreg ha hY hjt (hCols j hjt).1 (hCols j hjt).2 hs
    exact (hc i hi).trans (col_plus_early hjt i hi).symm

end GeneralEquality

theorem check_Lemma24 : Challenge.Lemma24 := by
  intro a b ha hb hab p q hreg
  have hp := (OneColumn.region_bounds hreg).1
  refine ⟨GeneralEquality.delta_gPlus (by omega) hp, ?_,
    GeneralEquality.plus_final_positive hreg ha hb hab,
    GeneralEquality.plus_value hreg ha hb hab, ?_⟩
  · intro j hj
    exact GeneralEquality.plus_psi_zero hreg ha hab hj
  · intro Y hY hLast hCols
    exact GeneralEquality.uniqueness hreg ha hab hY hLast hCols

#print axioms check_Lemma24
end CodexPaper1
