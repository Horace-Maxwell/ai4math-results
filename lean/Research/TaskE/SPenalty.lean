import Research.TaskE.SBasis

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.SProof
open Finset BackfillPaper1.Challenge

lemma penalty_scalar {L Z s t : ℝ} (hL : 0 ≤ L) (hZ : |Z| ≤ 1)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (htZ : 0 < t * Z) :
    max 0 (2 * L - 2 * |L * (Z - s)|) = if s = t then 2 * L * |Z| else 0 := by
  have hZ1 : Z ≤ 1 := (le_abs_self Z).trans hZ
  have hZ0 : -1 ≤ Z := by linarith [neg_abs_le Z]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · simp only [one_mul] at htZ
    rw [ite_eq_left rfl, abs_mul, abs_of_nonneg hL, abs_of_pos htZ,
      abs_of_nonpos (by linarith : Z - 1 ≤ 0)]
    have he : 2 * L - 2 * (L * -(Z - 1)) = 2 * L * Z := by ring
    rw [he, max_eq_right (mul_nonneg (mul_nonneg (by norm_num) hL) htZ.le)]
  · simp only [neg_one_mul] at htZ
    rw [ite_eq_right (by norm_num : (1 : ℝ) ≠ -1), abs_mul, abs_of_nonneg hL,
      abs_of_nonpos (by linarith : Z - 1 ≤ 0)]
    apply max_eq_left
    nlinarith [mul_nonneg hL (by linarith : 0 ≤ -Z)]
  · simp only [one_mul] at htZ
    rw [ite_eq_right (by norm_num : (-1 : ℝ) ≠ 1), abs_mul, abs_of_nonneg hL,
      abs_of_nonneg (by linarith : 0 ≤ Z - -1)]
    apply max_eq_left
    nlinarith [mul_nonneg hL htZ.le]
  · simp only [neg_one_mul] at htZ
    rw [ite_eq_left rfl, abs_mul, abs_of_nonneg hL, abs_of_neg (by linarith : Z < 0),
      abs_of_nonneg (by linarith : 0 ≤ Z - -1)]
    have he : 2 * L - 2 * (L * (Z - -1)) = 2 * L * -Z := by ring
    rw [he, max_eq_right (mul_nonneg (mul_nonneg (by norm_num) hL) htZ.le)]

lemma penalty_row {a j : ℕ} (ha : 1 ≤ a) (hj : j < a) {p : ℝ} (hp : 3 ≤ p)
    {c : ℕ → ℝ} (hc : IsSignVec a c) :
    max 0 (rowAbsSum a p (a - 1 - j) - 2 * |tMulVec a p c (a - 1 - j)|) =
      if c j = c (j + 1) then
        2 * (p ^ (a - 1) * (p - 1)) * |z p a c (j : ℤ)| else 0 := by
  have hrow := row_abs_mass a ha p hp (a - 1 - j) (by omega)
  rw [ite_eq_right (by omega : a - 1 - j ≠ a)] at hrow
  rw [hrow, row_path ha hj hp c]
  rw [show 2 * p ^ (a - 1) * (p - 1) = 2 * (p ^ (a - 1) * (p - 1)) by ring]
  exact penalty_scalar (mul_nonneg (pow_nonneg (by linarith) _) (by linarith))
    (path_bounds ha hj hp hc).2.2 (hc j hj.le) (hc (j + 1) (by omega))
    (path_bounds ha hj hp hc).1

lemma penalty_identity : CodexPaper1.TaskE.Challenge.NonlastPenaltyIdentity := by
  classical
  intro a ha p hp c hc
  let f : ℕ → ℝ := fun i => max 0 (rowAbsSum a p i - 2 * |tMulVec a p c i|)
  calc
    _ = ∑ j ∈ range a, f (a - 1 - j) := (sum_range_reflect f a).symm
    _ = ∑ j ∈ range a, if c j = c (j + 1) then
          2 * (p ^ (a - 1) * (p - 1)) * |z p a c (j : ℤ)| else 0 := by
      apply sum_congr rfl
      intro j hj
      exact penalty_row ha (mem_range.mp hj) hp hc
    _ = _ := by
      rw [NA, sum_filter, mul_sum]
      apply sum_congr rfl
      intro j _hj
      split_ifs <;> ring

lemma budget_gap {a : ℕ} (ha : 1 ≤ a) {p : ℝ} (hp : 3 ≤ p)
    {c : ℕ → ℝ} (hc : IsSignVec a c) :
    2 * DeltaC a p c -
      (∑ i ∈ range a, max 0 (rowAbsSum a p i - 2 * |tMulVec a p c i|)) =
    ∑ j ∈ NA a c, 2 * p ^ (a - 1) *
      (2 * p * mu p (j : ℤ) - (p - 1)) * |z p a c (j : ℤ)| := by
  rw [deficit_identity hp hc, penalty_identity a ha p hp c hc]
  have hw : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel ha]
  rw [hw]
  simp_rw [mul_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _hj
  ring

lemma coefficient_nonneg {p : ℝ} (hp : 3 ≤ p) (j : ℕ) :
    0 ≤ 2 * p * mu p (j : ℤ) - (p - 1) := by
  have hp0 : 0 < p := by linarith
  have h := (div_le_iff₀ hp0).mp (mu_lower hp j)
  nlinarith

lemma coefficient_pos {p : ℝ} (hp : 5 ≤ p) (j : ℕ) :
    0 < 2 * p * mu p (j : ℤ) - (p - 1) := by
  have hp0 : 0 < p := by linarith
  have h := (div_le_iff₀ hp0).mp (mu_lower (by linarith : 3 ≤ p) j)
  nlinarith

lemma penalty_bound : CodexPaper1.TaskE.Challenge.NonlastPenaltyBound := by
  intro a ha p hp c hc
  have h := budget_gap ha hp hc
  have hn : 0 ≤ ∑ j ∈ NA a c, 2 * p ^ (a - 1) *
      (2 * p * mu p (j : ℤ) - (p - 1)) * |z p a c (j : ℤ)| := by
    apply sum_nonneg
    intro j _hj
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _))
      (coefficient_nonneg hp j)) (abs_nonneg _)
  linarith

lemma penalty_strict : CodexPaper1.TaskE.Challenge.NonlastPenaltyStrict := by
  classical
  intro a ha p hp c hc hna
  have hp3 : 3 ≤ p := by linarith
  have hp0 : 0 < p := by linarith
  have h := budget_gap ha hp3 hc
  have hn : 0 < ∑ j ∈ NA a c, 2 * p ^ (a - 1) *
      (2 * p * mu p (j : ℤ) - (p - 1)) * |z p a c (j : ℤ)| := by
    apply sum_pos'
    · intro j _hj
      exact mul_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) (pow_nonneg hp0.le _))
        (coefficient_pos hp j).le) (abs_nonneg _)
    · obtain ⟨j, hj, he⟩ := Additional.exists_repeat_of_not_pmAlt hc hna
      refine ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, he⟩, ?_⟩
      have hz : 0 < |z p a c (j : ℤ)| := lt_of_lt_of_le
        (div_pos (by linarith) hp0) (path_bounds ha hj hp3 hc).2.1
      exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos hp0 _))
        (coefficient_pos hp j)) hz
  linarith

end CodexPaper1.TaskE.SProof
#print axioms CodexPaper1.TaskE.SProof.penalty_identity
#print axioms CodexPaper1.TaskE.SProof.penalty_bound
#print axioms CodexPaper1.TaskE.SProof.penalty_strict
