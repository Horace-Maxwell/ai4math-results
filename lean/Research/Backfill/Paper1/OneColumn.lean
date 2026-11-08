import Research.Backfill.Paper1.Additional

/-!
Proof source for the full frozen Lemma22. Acceptance evidence is recorded
separately by check_onecolumn.py; the source alone is not an acceptance receipt.
The argument works for every column length, not only the old a = 2 case.
Frozen Paper1 Challenge: 88900a3e49be210812de76aed47d0c6baa2534159f0389fe7b68d2fdc1f5d9a2.
-/
set_option autoImplicit false

namespace CodexPaper1
open BackfillPaper1 Finset ICGGeneral

namespace OneColumn

lemma region_bounds {p q : ℝ} (h : Challenge.Regions p q) :
    2 < p ∧ 2 ≤ q - 1 ∧ 1 ≤ (q - 1) * ((p - 2) / p) := by
  rcases h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hp0 : 0 < p := by linarith
    refine ⟨by linarith, by linarith, ?_⟩
    rw [← mul_div_assoc, le_div_iff₀ hp0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ p - 2 by linarith)]
  · subst p
    refine ⟨by norm_num, by linarith, ?_⟩
    norm_num
    linarith

lemma tau_unit_bound {p : ℝ} (hp : 2 < p) {a : ℕ} {ζ : ℕ → ℝ}
    (hζ : ∀ i ≤ a, |ζ i| ≤ 1) {j : ℕ} (hj : j < a) :
    |tau p a ζ j| ≤ 2 * ((p - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ (p - 1) / p := div_nonneg (by linarith) hp0.le
  rw [tau_eq hp0.ne' ζ hj, abs_mul, abs_of_nonneg hr]
  have hz := Zp_abs_le (by linarith : 1 ≤ p) hζ (j + 1) hj
  have hb : |ζ j - Zp p a ζ (j + 1)| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [hζ j hj.le])
  nlinarith

lemma tau_alt_lower {p : ℝ} (hp : 2 < p) {a j : ℕ} (hj : j < a) :
    (p - 1) / p ≤ |tau p a sgnv j| := by
  have hp0 : 0 < p := by linarith
  have hr : 0 ≤ (p - 1) / p := div_nonneg (by linarith) hp0.le
  have hs := Zp_sign hp.le (sgnv_isSign a) (j + 1) hj
  have hd : 0 ≤ (p - 2) / p := div_nonneg (by linarith) hp0.le
  rw [sgnv_succ] at hs
  have hdiff : 1 ≤ |sgnv j - Zp p a sgnv (j + 1)| := by
    rcases sgnv_isSign a j hj.le with h | h
    · rw [h] at hs ⊢
      rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    · rw [h] at hs ⊢
      rw [abs_of_nonpos (by nlinarith)]
      nlinarith
  rw [tau_eq hp0.ne' sgnv hj, abs_mul, abs_of_nonneg hr]
  nlinarith

lemma Tv_abs_row {p : ℝ} (hp : 0 < p) (a : ℕ) (w : ℕ → ℝ)
    {i : ℕ} (hi : i < a) :
    |Tv p a w i| = p ^ a * |tau p a w (a - 1 - i)| := by
  have hidx : a - 1 - i + i + 1 = a := by omega
  have hrow := Tv_row hp.ne' (a - 1 - i) i w
  rw [hidx] at hrow
  rw [hrow, abs_mul, abs_of_pos (pow_pos hp a), abs_sub_comm]
  rfl

lemma alt_row_dominates {p q : ℝ} (hpq : Challenge.Regions p q)
    (a : ℕ) {ζ : ℕ → ℝ} (hζ : ∀ i ≤ a, |ζ i| ≤ 1)
    {i : ℕ} (hi : i ≤ a) :
    |Tv p a ζ i| ≤ (q - 1) * |Tv p a sgnv i| := by
  obtain ⟨hp, hq, hlast⟩ := region_bounds hpq
  have hp0 : 0 < p := by linarith
  have hq0 : 0 ≤ q - 1 := by linarith
  by_cases hia : i = a
  · subst i
    rw [Tv_last hp0.ne', Tv_last hp0.ne', abs_mul, abs_mul,
      abs_of_pos (pow_pos hp0 a)]
    have hz := Zp_abs_le (by linarith : 1 ≤ p) hζ 0 (Nat.zero_le _)
    have hs : (p - 2) / p ≤ |Zp p a sgnv 0| := by
      rw [Zp_abs_eq hp.le (sgnv_isSign a) (Nat.zero_le _)]
      exact Zp_sign hp.le (sgnv_isSign a) 0 (Nat.zero_le _)
    have hh : |Zp p a ζ 0| ≤ (q - 1) * |Zp p a sgnv 0| :=
      hz.trans (hlast.trans (mul_le_mul_of_nonneg_left hs hq0))
    nlinarith [mul_le_mul_of_nonneg_left hh (pow_pos hp0 a).le]
  · have hit : i < a := lt_of_le_of_ne hi hia
    have hj : a - 1 - i < a := by omega
    rw [Tv_abs_row hp0 a ζ hit, Tv_abs_row hp0 a sgnv hit]
    have hz := tau_unit_bound hp hζ hj
    have hs := tau_alt_lower hp hj
    have hr : 0 ≤ (p - 1) / p := div_nonneg (by linarith) hp0.le
    have hh : |tau p a ζ (a - 1 - i)| ≤ (q - 1) * |tau p a sgnv (a - 1 - i)| := by
      nlinarith [mul_le_mul_of_nonneg_left hs hq0,
        mul_le_mul_of_nonneg_right hq hr]
    nlinarith [mul_le_mul_of_nonneg_left hh (pow_pos hp0 a).le]

lemma pmAlt_abs_Tv {p : ℝ} {a : ℕ} {c : ℕ → ℝ}
    (hc : Challenge.IsPmAlt a c) (i : ℕ) : |Tv p a c i| = |Tv p a sgnv i| := by
  rcases hc with h | h
  · change (∀ j ≤ a, c j = sgnv j) at h
    rw [Tv_congr p a h i]
  · change (∀ j ≤ a, c j = -sgnv j) at h
    rw [Tv_congr p a h i]
    have hn := Tv_smul p a (-1) sgnv i
    simp only [neg_one_mul] at hn
    rw [hn, abs_neg]

lemma delta_pmAlt {p : ℝ} {a : ℕ} {c : ℕ → ℝ}
    (hc : Challenge.IsPmAlt a c) : Challenge.DeltaC a p c = 0 := by
  unfold Challenge.DeltaC
  rw [Additional.dNorm_eq_L1, Additional.l1_tMulVec_eq_L1]
  have hL : L1 p a c = L1 p a sgnv := by
    unfold L1
    exact Finset.sum_congr rfl (fun i _ => pmAlt_abs_Tv hc i)
  rw [hL, sub_self]

end OneColumn

theorem check_Lemma22 : Challenge.Lemma22 := by
  intro a _ha p q hpq μ hμ0 hμ1 c ζ _hc hζ
  have hP := (OneColumn.region_bounds hpq).2.1
  have hμP : μ ≤ q - 1 := by linarith
  constructor
  · unfold Challenge.psi
    have hs :
        (∑ i ∈ range (a + 1), Challenge.hcell (q - 1) μ
          (Challenge.tMulVec a p c i) (Challenge.tMulVec a p ζ i)) ≤
        2 * μ * ∑ i ∈ range (a + 1),
          max 0 (|Challenge.tMulVec a p ζ i| - (q - 1) * |Challenge.tMulVec a p c i|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      exact hcell_le hμ0 hμ1 hμP _ _
    linarith
  · intro halt
    have hc : ∀ i ≤ a, Challenge.hcell (q - 1) μ
        (Challenge.tMulVec a p c i) (Challenge.tMulVec a p ζ i) ≤ 0 := by
      intro i hi
      apply hcell_nonpos hμ0 hμ1 hμP
      rw [Additional.tMulVec_eq_Tv p a ζ i hi,
        Additional.tMulVec_eq_Tv p a c i hi, OneColumn.pmAlt_abs_Tv halt]
      exact OneColumn.alt_row_dominates hpq a hζ hi
    have hs : (∑ i ∈ range (a + 1), Challenge.hcell (q - 1) μ
        (Challenge.tMulVec a p c i) (Challenge.tMulVec a p ζ i)) ≤ 0 :=
      Finset.sum_nonpos (fun i hi => hc i (by simpa using Finset.mem_range.mp hi))
    have hpsi : Challenge.psi a p q μ c ζ =
        -(∑ i ∈ range (a + 1), Challenge.hcell (q - 1) μ
          (Challenge.tMulVec a p c i) (Challenge.tMulVec a p ζ i)) := by
      simp [Challenge.psi, OneColumn.delta_pmAlt halt]
    refine ⟨hc, by rw [hpsi]; linarith, ?_⟩
    rw [hpsi, neg_eq_zero]
    constructor
    · intro hz i hi
      have hle := Finset.single_le_sum
        (f := fun j => -Challenge.hcell (q - 1) μ
          (Challenge.tMulVec a p c j) (Challenge.tMulVec a p ζ j))
        (fun j hj => neg_nonneg.mpr (hc j (by simpa using Finset.mem_range.mp hj)))
        (show i ∈ range (a + 1) by simpa using hi)
      rw [Finset.sum_neg_distrib, hz, neg_zero] at hle
      linarith [hc i hi]
    · intro hz
      exact Finset.sum_eq_zero (fun i hi => hz i (by simpa using Finset.mem_range.mp hi))

#print axioms check_Lemma22
end CodexPaper1
