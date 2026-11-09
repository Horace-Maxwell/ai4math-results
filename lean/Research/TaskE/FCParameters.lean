import Research.TaskE.ChallengeFC
import Research.Backfill.Paper1.MuSupplements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge ICGGeneral ICGEqualParity

lemma q_parameters {q : ℝ} (hq : 5 ≤ q) :
    0 < mu q 0 ∧ mu q 0 ≤ muInf q ∧ muInf q ≤ mu q 1 ∧ mu q 1 ≤ 1 := by
  have hm0 : mu q (0 : ℤ) = nu q 1 := by simpa using CodexPaper1.Additional.mu_nat_eq_nu q 0
  have hm1 : mu q (1 : ℤ) = nu q 2 := by simpa using CodexPaper1.Additional.mu_nat_eq_nu q 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm0]; exact nu_pos (by linarith) _
  · rw [hm0]; exact (nu_odd_lt (by linarith : 1 < q) (by decide : Odd 1)).le
  · rw [hm1]; exact (nu_even_gt (by linarith : 1 < q) (by decide : Even 2)).le
  · rw [hm1]; exact (nu_bounds (by linarith : 2 ≤ q) 2).2

lemma eta_unit {q y : ℝ} (hq : 5 ≤ q) (hy : 0 ≤ y ∧ y ≤ 1) (n : ℕ) :
    0 ≤ etaMap q n y ∧ etaMap q n y ≤ 1 := by
  have hq0 : 0 < q := by linarith
  induction n with
  | zero => exact hy
  | succ n ih =>
    change 0 ≤ (q - 1 - etaMap q n y) / q ∧ (q - 1 - etaMap q n y) / q ≤ 1
    constructor
    · exact div_nonneg (by linarith [ih.2]) hq0.le
    · rw [div_le_one hq0]; linarith [ih.1]

lemma initial_unit {a : ℕ} {q y : ℝ} (hq : 5 ≤ q)
    (hy : if Even a then mu q 0 ≤ y ∧ y ≤ muInf q
      else muInf q ≤ y ∧ y ≤ mu q 1) : 0 ≤ y ∧ y ≤ 1 := by
  obtain ⟨hm0, h0L, hL1, hm1⟩ := q_parameters hq
  split_ifs at hy with he
  · exact ⟨hm0.le.trans hy.1, hy.2.trans (hL1.trans hm1)⟩
  · exact ⟨(hm0.le.trans h0L).trans hy.1, hy.2.trans hm1⟩

lemma two_delta_three (a : ℕ) :
    2 * deltaK a 3 = (3 : ℝ) ^ a + (-1) ^ a := by
  unfold deltaK
  norm_num
  ring

lemma pow_three_ge {a : ℕ} (ha : 3 ≤ a) : (27 : ℝ) ≤ 3 ^ a := by
  calc
    (27 : ℝ) = 3 ^ (3 : ℕ) := by norm_num
    _ ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) ha

lemma two_delta_upper {a : ℕ} (ha : 3 ≤ a) :
    2 * deltaK a 3 ≤ (28 / 27 : ℝ) * 3 ^ a := by
  rw [two_delta_three]
  have hp := pow_three_ge ha
  have hs : (-1 : ℝ) ^ a ≤ 1 := by
    rcases neg_one_pow_eq_or ℝ a with h | h <;> norm_num [h]
  nlinarith

lemma delta_three_pos {a : ℕ} (ha : 3 ≤ a) : 0 < deltaK a 3 := by
  have he := two_delta_three a
  have hp := pow_three_ge ha
  have hs : -1 ≤ (-1 : ℝ) ^ a := by
    rcases neg_one_pow_eq_or ℝ a with h | h <;> norm_num [h]
  linarith

lemma family_bounds {a : ℕ} {q : ℝ} (hq : 5 ≤ q) {t : ℝ × ℝ × ℝ}
    (ht : FamF a q t) :
    (0 ≤ t.1 ∧ t.1 ≤ 1) ∧ (0 ≤ t.2.1 ∧ t.2.1 ≤ 1) ∧ q * t.2.2 < q - 1 := by
  obtain ⟨hm0, h0L, hL1, hm1⟩ := q_parameters hq
  have hq0 : 0 < q := by linarith
  have hL0 : 0 < muInf q := hm0.trans_le h0L
  have hLle : muInf q ≤ 1 := hL1.trans hm1
  have hrec : q * mu q 1 = q - 1 - mu q 0 := by
    have hzero : mu q (0 : ℤ) = nu q 1 := by simpa using CodexPaper1.Additional.mu_nat_eq_nu q 0
    have hone : mu q (1 : ℤ) = nu q 2 := by simpa using CodexPaper1.Additional.mu_nat_eq_nu q 1
    rw [hzero, hone, show (2 : ℕ) = 1 + 1 from rfl, nu_succ]
    field_simp
  have hqmu : q * mu q 1 < q - 1 := by linarith
  have hqL : q * muInf q < q - 1 :=
    (mul_le_mul_of_nonneg_left hL1 hq0.le).trans_lt hqmu
  have hdiv (m : ℝ) (hm : 0 < m) : q * ((q - 1 - m) / q) < q - 1 := by
    field_simp
    linarith
  unfold FamF at ht
  dsimp only at ht
  split_ifs at ht with he
  · rcases ht with ⟨hu, hm0', hmL, hr⟩ | ⟨hm, hu0, huL, hr⟩ |
        ⟨huL, hu1, hm0', hmL, hr⟩ | ⟨hu0, huL, hmL, hm1', hr⟩
    · rw [hu, hr]
      exact ⟨⟨by norm_num, le_rfl⟩, ⟨hm0.le.trans hm0', hmL.trans hLle⟩,
        hdiv _ (hm0.trans_le hm0')⟩
    · rw [hm, hr]
      exact ⟨⟨hm0.le.trans hu0, huL.trans hLle⟩, ⟨by norm_num, le_rfl⟩,
        hdiv _ (hm0.trans_le hu0)⟩
    · rw [hr]
      exact ⟨⟨hL0.le.trans huL, hu1.trans hm1⟩,
        ⟨hm0.le.trans hm0', hmL.trans hLle⟩,
        (mul_le_mul_of_nonneg_left hu1 hq0.le).trans_lt hqmu⟩
    · rw [hr]
      exact ⟨⟨hm0.le.trans hu0, huL.trans hLle⟩,
        ⟨hL0.le.trans hmL, hm1'.trans hm1⟩,
        (mul_le_mul_of_nonneg_left hm1' hq0.le).trans_lt hqmu⟩
  · rcases ht with ⟨hu, hm, hr⟩ | ⟨hu, hmL, hm1', hr⟩ | ⟨hm, huL, hu1, hr⟩ |
        ⟨hbox, hr⟩
    · rw [hu, hm, hr]
      exact ⟨⟨by norm_num, le_rfl⟩, ⟨by norm_num, le_rfl⟩,
        (mul_le_mul_of_nonneg_left (h0L.trans hL1) hq0.le).trans_lt hqmu⟩
    · rw [hu, hr]
      exact ⟨⟨by norm_num, le_rfl⟩, ⟨hL0.le.trans hmL, hm1'.trans hm1⟩,
        hdiv _ (hL0.trans_le hmL)⟩
    · rw [hm, hr]
      exact ⟨⟨hL0.le.trans huL, hu1.trans hm1⟩, ⟨by norm_num, le_rfl⟩,
        hdiv _ (hL0.trans_le huL)⟩
    · rw [hr]
      rcases hbox with ⟨hu0, huL, hm0', hmL⟩ | ⟨huL, hu1, hmL, hm1'⟩
      · exact ⟨⟨hm0.le.trans hu0, huL.trans hLle⟩,
          ⟨hm0.le.trans hm0', hmL.trans hLle⟩, hqL⟩
      · exact ⟨⟨hL0.le.trans huL, hu1.trans hm1⟩,
          ⟨hL0.le.trans hmL, hm1'.trans hm1⟩, hqL⟩

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.family_bounds
