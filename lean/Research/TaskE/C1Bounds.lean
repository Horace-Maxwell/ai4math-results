import Research.TaskE.ChallengeC1
import Research.TaskE.PotentialLower
import Research.TaskE.DeficitLower
import Research.TaskE.FCParameters

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge ICGGeneral

lemma mu_zero_lower {q : ℝ} (hq : 5 ≤ q) : (3 / 5 : ℝ) ≤ mu q 0 := by
  rw [(CodexPaper1.check_MuBounds q (by linarith)).2.2.1]
  rw [le_div_iff₀ (show 0 < q by linarith)]
  linarith

lemma q_mu_one {q : ℝ} (hq : 5 ≤ q) : q * mu q 1 = q - 1 - mu q 0 := by
  have hzero : mu q (0 : ℤ) = nu q 1 := by simpa using CodexPaper1.Additional.mu_nat_eq_nu q 0
  have hone : mu q (1 : ℤ) = nu q 2 := by simpa using CodexPaper1.Additional.mu_nat_eq_nu q 1
  rw [hzero, hone, show (2 : ℕ) = 1 + 1 from rfl, nu_succ]
  field_simp

lemma eta_lower_mu {q y : ℝ} (hq : 5 ≤ q) (hy : 0 ≤ y ∧ y ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) : mu q 0 ≤ etaMap q n y := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hb := (eta_unit hq hy k).2
  rw [(CodexPaper1.check_MuBounds q (by linarith)).2.2.1]
  change (q - 2) / q ≤ (q - 1 - etaMap q k y) / q
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ q)
  linarith

lemma eta_upper_mu {q y : ℝ} (hq : 5 ≤ q) (hy : 0 ≤ y ∧ y ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) : etaMap q n y ≤ mu q 1 := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [hk]
  have hb := eta_lower_mu hq hy (n := k + 1) (by omega)
  have hr := q_mu_one hq
  have he : mu q 1 = (q - 1 - mu q 0) / q := by
    rw [eq_div_iff (show q ≠ 0 by linarith)]
    nlinarith
  rw [he]
  change (q - 1 - etaMap q (k + 1) y) / q ≤ (q - 1 - mu q 0) / q
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ q)
  linarith

lemma eta_times_q {q y : ℝ} (hq : 5 ≤ q) (hy : 0 ≤ y ∧ y ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) : 0 < q * etaMap q n y ∧ q * etaMap q n y ≤ q - 1 := by
  have hp := (q_parameters hq).1.trans_le (eta_lower_mu hq hy hn)
  have hq0 : 0 < q := by linarith
  refine ⟨mul_pos hq0 hp, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hb := (eta_unit hq hy k).1
  change q * ((q - 1 - etaMap q k y) / q) ≤ q - 1
  have he : q * ((q - 1 - etaMap q k y) / q) = q - 1 - etaMap q k y := by field_simp
  rw [he]
  linarith

lemma chain_zeta_unit {a : ℕ} {q : ℝ} (hq : 5 ≤ q) {g : ℕ → ℝ}
    (hg : IsSignVec a g) (k : ℕ) :
    ∀ i ≤ a, |(-1) ^ k * mu q ((k : ℤ) - 1) * g i| ≤ 1 := by
  intro i hi
  have hm : 0 ≤ mu q ((k : ℤ) - 1) ∧ mu q ((k : ℤ) - 1) ≤ 1 := by
    rw [CodexPaper1.Additional.mu_pred_eq_nu]
    exact ⟨(nu_pos (by linarith) _).le, (nu_bounds (by linarith : 2 ≤ q) _).2⟩
  have hs : |(-1 : ℝ) ^ k| = 1 := by simp [abs_pow]
  have hgi : |g i| = 1 := by rcases hg i hi with h | h <;> norm_num [h]
  rw [abs_mul, abs_mul, hs, one_mul, abs_of_nonneg hm.1, hgi, mul_one]
  exact hm.2

lemma chain_sum_nonneg {a : ℕ} {q y : ℝ} (hq : 5 ≤ q)
    (hy : 0 ≤ y ∧ y ≤ 1) {g : ℕ → ℝ} (hg : IsSignVec a g) (k : ℕ) :
    0 ≤ ∑ n ∈ Icc 1 k, (q - 1) * (1 + etaMap q n y) * DeltaC a 3 g := by
  have hd := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hg
  apply sum_nonneg
  intro n _hn
  exact mul_nonneg (mul_nonneg (by linarith) (by linarith [(eta_unit hq hy n).1])) hd

lemma chain_sum_two {a k : ℕ} {q y : ℝ} (hq : 5 ≤ q) (hy : 0 ≤ y ∧ y ≤ 1)
    {g : ℕ → ℝ} (hg : IsSignVec a g) (hk : 2 ≤ k) :
    2 * ((q - 1) * (1 + mu q 0) * DeltaC a 3 g) ≤
      ∑ n ∈ Icc 1 k, (q - 1) * (1 + etaMap q n y) * DeltaC a 3 g := by
  have hd := CodexPaper1.Prop31.delta_nonneg (p := (3 : ℝ)) (by norm_num) hg
  have hm (n : ℕ) (hn : 1 ≤ n) :
      (q - 1) * (1 + mu q 0) * DeltaC a 3 g ≤
        (q - 1) * (1 + etaMap q n y) * DeltaC a 3 g := by
    have h := mul_le_mul_of_nonneg_right (eta_lower_mu hq hy hn)
      (mul_nonneg (by linarith : 0 ≤ q - 1) hd)
    nlinarith
  have hs : 2 * ((q - 1) * (1 + mu q 0) * DeltaC a 3 g) ≤
      ∑ n ∈ Icc 1 2, (q - 1) * (1 + etaMap q n y) * DeltaC a 3 g := by
    rw [show Icc (1 : ℕ) 2 = {1, 2} by decide]
    simp only [sum_insert, mem_singleton, show (1 : ℕ) ≠ 2 by decide,
      not_false_eq_true, sum_singleton]
    linarith [hm 1 (by omega), hm 2 (by omega)]
  apply hs.trans
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hk)
  intro n _hn _hn'
  exact mul_nonneg (mul_nonneg (by linarith) (by linarith [(eta_unit hq hy n).1])) hd

lemma gamma_upper {a : ℕ} (ha : 3 ≤ a) {g : ℕ → ℝ}
    (hg : IsSignVec a g) (hna : ¬ IsPmAlt a g) :
    2 * deltaK a 3 - DeltaC a 3 g ≤ (5 / 2 : ℝ) * DeltaC a 3 g := by
  have hd := deficit_lower a ha g hg hna
  have hδ := two_delta_upper ha
  nlinarith

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.chain_sum_two
#print axioms CodexPaper1.TaskE.FCProof.eta_upper_mu
