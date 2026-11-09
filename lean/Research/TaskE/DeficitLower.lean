import Research.TaskE.ChallengeFC
import Research.TaskE.SBasis
import Research.Backfill.Paper1.MuSupplements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge ICGGeneral ICGEqualParity

lemma mu_three_zero : mu 3 0 = (1 / 3 : ℝ) := by
  norm_num [mu, muSeq]

lemma mu_three_one : mu 3 1 = (5 / 9 : ℝ) := by
  norm_num [mu, muSeq]

lemma mu_three_positive_index {j : ℕ} (hj : 1 ≤ j) :
    (4 / 9 : ℝ) ≤ mu 3 (j : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hu := ((CodexPaper1.check_MuBounds 3 (by norm_num)).2.1 k).2
  rw [mu_three_one, CodexPaper1.Additional.mu_nat_eq_nu] at hu
  rw [CodexPaper1.Additional.mu_nat_eq_nu, nu_succ]
  linarith

lemma deficit_pays_term {a j : ℕ} (ha : 1 ≤ a) {c : ℕ → ℝ}
    (hc : IsSignVec a c) (hj : j ∈ NA a c) :
    2 * (3 : ℝ) ^ a * (mu 3 (j : ℤ) * |z 3 a c (j : ℤ)|) ≤ DeltaC a 3 c := by
  have _ha_use : 0 < a := lt_of_lt_of_le (by norm_num : 0 < 1) ha
  rw [SProof.deficit_identity (by norm_num : (3 : ℝ) ≤ 3) hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply single_le_sum _ hj
  intro i _hi
  exact mul_nonneg (by have h := SProof.mu_lower (p := 3) (by norm_num) i; linarith)
    (abs_nonneg _)

lemma deficit_lower : CodexPaper1.TaskE.Challenge.DeficitLowerThree := by
  classical
  intro a ha c hc hna
  have ha1 : 1 ≤ a := by omega
  by_cases hj : ∃ j, 1 ≤ j ∧ j < a ∧ c j = c (j + 1)
  · obtain ⟨j, hj1, hja, he⟩ := hj
    have hp := deficit_pays_term ha1 hc (j := j) (by exact mem_filter.mpr ⟨mem_range.mpr hja, he⟩)
    have hm := mu_three_positive_index hj1
    have hz := (SProof.path_bounds ha1 hja (by norm_num : (3 : ℝ) ≤ 3) hc).2.1
    norm_num at hz
    have ht : (4 / 27 : ℝ) ≤ mu 3 (j : ℤ) * |z 3 a c (j : ℤ)| := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ mu 3 (j : ℤ) - 4 / 9)
        (by linarith : 0 ≤ |z 3 a c (j : ℤ)| - 1 / 3)]
    nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * (3 : ℝ) ^ a by positivity)]
  · have hn : ∀ j, 1 ≤ j → j < a → c j ≠ c (j + 1) := by
      intro j hj1 hja he
      exact hj ⟨j, hj1, hja, he⟩
    obtain ⟨j, hja, he⟩ := CodexPaper1.Additional.exists_repeat_of_not_pmAlt hc hna
    have hj0 : j = 0 := by by_contra h; exact hn j (by omega) hja he
    subst j
    have hs1 := Zp_step_alt (x := (3 : ℝ)) (by norm_num) hc
      (k := 1) (by omega) (hn 1 (by omega) (by omega))
    have hs2 := Zp_step_alt (x := (3 : ℝ)) (by norm_num) hc
      (k := 2) (by omega) (hn 2 (by omega) (by omega))
    have hz3 := (SProof.path_bounds ha1 (j := 2) (by omega)
      (by norm_num : (3 : ℝ) ≤ 3) hc).2.1
    rw [CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a c 2 (by omega)] at hz3
    norm_num at hs1 hs2 hz3
    have hz0 : (4 / 9 : ℝ) ≤ |z 3 a c (0 : ℤ)| := by
      have hz_eq : z 3 a c (0 : ℤ) = Zp 3 a c 1 := by
        simpa using CodexPaper1.Additional.z_nat_eq_Zp (x := (3 : ℝ)) (by norm_num) a c 0 (by omega)
      rw [hz_eq]
      linarith
    have hp := deficit_pays_term ha1 hc (j := 0) (by simp [NA, he]; omega)
    change 2 * (3 : ℝ) ^ a * (mu 3 (0 : ℤ) * |z 3 a c (0 : ℤ)|) ≤ DeltaC a 3 c at hp
    rw [mu_three_zero] at hp
    nlinarith [mul_le_mul_of_nonneg_left hz0 (show 0 ≤ 2 * (3 : ℝ) ^ a / 3 by positivity)]

lemma deficit_odd_lower {a : ℕ} (ha : 1 ≤ a) (hodd : Odd a)
    {c : ℕ → ℝ} (hc : IsSignVec a c) (hna : ¬ IsPmAlt a c) :
    (1 / 3 : ℝ) * 3 ^ a ≤ DeltaC a 3 c := by
  classical
  have hne : (NA a c).Nonempty := by
    obtain ⟨j, hj, he⟩ := CodexPaper1.Additional.exists_repeat_of_not_pmAlt hc hna
    exact ⟨j, by simp [NA, hj, he]⟩
  let J := (NA a c).max' hne
  have hJ : J ∈ NA a c := max'_mem _ _
  have hja : J < a := (mem_filter.mp hJ).1 |> mem_range.mp
  have halt : ∀ i, J + 1 ≤ i → i < a → c i ≠ c (i + 1) := by
    intro i hi hia he
    have him : i ∈ NA a c := by simp [NA, hia, he]
    have hle := le_max' (NA a c) i him
    change i ≤ J at hle
    omega
  have ht := Zp_alt_tail (x := (3 : ℝ)) (by norm_num) hc
    (a - (J + 1)) (J + 1) (by omega) halt
  have hz : |z 3 a c (J : ℤ)| = nu 3 (a - (J + 1)) := by
    rw [CodexPaper1.Additional.z_nat_eq_Zp (by norm_num) a c J hja, ht]
  have hp := deficit_pays_term ha hc hJ
  rw [hz, CodexPaper1.Additional.mu_nat_eq_nu] at hp
  have h0 := (nu_bounds (x := (3 : ℝ)) (by norm_num) (J + 1)).1
  have h1 := (nu_bounds (x := (3 : ℝ)) (by norm_num) (a - (J + 1))).1
  have hprod : (1 / 6 : ℝ) ≤ nu 3 (J + 1) * nu 3 (a - (J + 1)) := by
    rcases Nat.even_or_odd (J + 1) with he | ho
    · have he' := nu_even_gt (x := (3 : ℝ)) (by norm_num) he
      norm_num at h0 h1 he'
      nlinarith [mul_nonneg (by linarith : 0 ≤ nu 3 (J + 1) - 1 / 2)
        (by linarith : 0 ≤ nu 3 (a - (J + 1)) - 1 / 3)]
    · have he : Even (a - (J + 1)) := by
        rw [Nat.even_iff]
        have hm := Nat.odd_iff.mp hodd
        have hj := Nat.odd_iff.mp ho
        omega
      have he' := nu_even_gt (x := (3 : ℝ)) (by norm_num) he
      norm_num at h0 h1 he'
      nlinarith [mul_nonneg (by linarith : 0 ≤ nu 3 (J + 1) - 1 / 3)
        (by linarith : 0 ≤ nu 3 (a - (J + 1)) - 1 / 2)]
  nlinarith [mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * (3 : ℝ) ^ a by positivity)]

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.deficit_lower
#print axioms CodexPaper1.TaskE.FCProof.deficit_odd_lower
