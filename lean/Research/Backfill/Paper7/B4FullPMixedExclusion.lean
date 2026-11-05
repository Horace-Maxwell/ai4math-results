import Research.Backfill.Paper7.B4MixedPolynomial

/-! Source-only exclusion of arbitrary nonzero Q when every P coordinate
is positive. A minimum of four actual local roots gives a small spectral root. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem mixed_local_antitone (p q : ℕ) (hp : 0 < p) (x y : ℝ)
    (hxy : x ≤ y) (hy1 : y ≤ 1) :
    mixedLocalPolynomial p q y ≤ mixedLocalPolynomial p q x := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hcoef : 0 ≤ (p : ℝ)+q+1-x-y := by linarith only [hpR,hqR,hxy,hy1]
  have hprod := mul_nonneg (sub_nonneg.mpr hxy) hcoef
  unfold mixedLocalPolynomial
  nlinarith only [hprod]
#print axioms Paper7B4Analytic.mixed_local_antitone

theorem mixed_local_small_root (p q : ℕ) (hp : 0 < p) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ mixedLocalPolynomial p q r = 0 ∧
      (0 < q → r < 1) := by
  have h0 : mixedLocalPolynomial p q 0 = (p : ℝ) := by unfold mixedLocalPolynomial; ring
  have h1 : mixedLocalPolynomial p q 1 = -(q : ℝ) := by unfold mixedLocalPolynomial; ring
  by_cases hq0 : q = 0
  · refine ⟨1,by norm_num,le_rfl,?_,?_⟩
    · simpa only [hq0,Nat.cast_zero,neg_zero] using h1
    · intro hq
      omega
  have hq : 0 < q := Nat.pos_of_ne_zero hq0
  let f : ℝ → ℝ := fun t => -mixedLocalPolynomial p q t
  have hcont : Continuous f := by dsimp [f,mixedLocalPolynomial]; fun_prop
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 0) (f 1) := by
    dsimp [f]
    rw [h0,h1]
    constructor <;> linarith
  obtain ⟨r,hr,hfr⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzero
  have hAr : mixedLocalPolynomial p q r = 0 := by
    change -mixedLocalPolynomial p q r = 0 at hfr
    linarith only [hfr]
  exact ⟨r,hr.1,hr.2.le,hAr,fun _ => hr.2⟩
#print axioms Paper7B4Analytic.mixed_local_small_root

theorem mixed_full_p_test_point (p q : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (hq : ∃ i, 0 < q i) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ mixedPolynomial p q r ≤ 0 := by
  have hex (i : Fin 4) := mixed_local_small_root (p i) (q i) (hp i)
  choose s hs0 hs1 hsA hsstrict using hex
  let r : ℝ := min (min (s 0) (s 1)) (min (s 2) (s 3))
  have hr0 : 0 < r := lt_min (lt_min (hs0 0) (hs0 1)) (lt_min (hs0 2) (hs0 3))
  have hrle (i : Fin 4) : r ≤ s i := by
    fin_cases i
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hr1 : r < 1 := by
    obtain ⟨i,hi⟩ := hq
    exact (hrle i).trans_lt (hsstrict i hi)
  have hAr (i : Fin 4) : 0 ≤ mixedLocalPolynomial (p i) (q i) r := by
    have hh := mixed_local_antitone (p i) (q i) (hp i) r (s i) (hrle i) (hs1 i)
    rw [hsA i] at hh
    exact hh
  have hrmem : ∃ i : Fin 4, r = s i := by
    rcases min_choice (min (s 0) (s 1)) (min (s 2) (s 3)) with hleft | hright
    · rcases min_choice (s 0) (s 1) with h0 | h1
      · exact ⟨0,hleft.trans h0⟩
      · exact ⟨1,hleft.trans h1⟩
    · rcases min_choice (s 2) (s 3) with h2 | h3
      · exact ⟨2,hright.trans h2⟩
      · exact ⟨3,hright.trans h3⟩
  obtain ⟨i,hi⟩ := hrmem
  have hAi : mixedLocalPolynomial (p i) (q i) r = 0 := by rw [hi]; exact hsA i
  have hprod : mixedLocalPolynomial (p 0) (q 0) r * mixedLocalPolynomial (p 1) (q 1) r *
      mixedLocalPolynomial (p 2) (q 2) r * mixedLocalPolynomial (p 3) (q 3) r = 0 := by
    fin_cases i
    · change mixedLocalPolynomial (p 0) (q 0) r = 0 at hAi
      simp only [hAi,zero_mul]
    · change mixedLocalPolynomial (p 1) (q 1) r = 0 at hAi
      simp only [hAi,mul_zero,zero_mul]
    · change mixedLocalPolynomial (p 2) (q 2) r = 0 at hAi
      simp only [hAi,mul_zero,zero_mul]
    · change mixedLocalPolynomial (p 3) (q 3) r = 0 at hAi
      simp only [hAi,mul_zero]
  have hscale : 0 ≤ r*(r-1)^2 := mul_nonneg hr0.le (sq_nonneg _)
  have h02 : 0 ≤ mixedLocalPolynomial (p 0) (q 0) r + mixedLocalPolynomial (p 2) (q 2) r :=
    add_nonneg (hAr 0) (hAr 2)
  have h13 : 0 ≤ mixedLocalPolynomial (p 1) (q 1) r + mixedLocalPolynomial (p 3) (q 3) r :=
    add_nonneg (hAr 1) (hAr 3)
  have hnonneg := mul_nonneg (mul_nonneg hscale h02) h13
  refine ⟨r,hr0,hr1,?_⟩
  unfold mixedPolynomial
  rw [hprod]
  linarith only [hnonneg]
#print axioms Paper7B4Analytic.mixed_full_p_test_point

theorem mixed_full_p_small_root (p q : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (hq : ∃ i, 0 < q i) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ mixedPolynomial p q t = 0 := by
  obtain ⟨r,hr0,hr1,hFr⟩ := mixed_full_p_test_point p q hp hq
  have hF0eq : mixedPolynomial p q 0 = (p 0 : ℝ)*p 1*p 2*p 3 := by
    unfold mixedPolynomial mixedLocalPolynomial
    ring
  have hF0 : 0 < mixedPolynomial p q 0 := by
    rw [hF0eq]
    exact mul_pos (mul_pos (mul_pos (by exact_mod_cast hp 0) (by exact_mod_cast hp 1))
      (by exact_mod_cast hp 2)) (by exact_mod_cast hp 3)
  have hcont : Continuous (mixedPolynomial p q) := by
    unfold mixedPolynomial mixedLocalPolynomial
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (mixedPolynomial p q r) (mixedPolynomial p q 0) :=
    ⟨hFr,hF0.le⟩
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' hr0.le hcont.continuousOn hzero
  have ht0 : 0 < t := by
    by_contra hh
    have htz : t = 0 := by linarith [ht.1]
    rw [htz] at hft
    linarith only [hF0,hft]
  exact ⟨t,ht0,ht.2.trans_lt hr1,hft⟩
#print axioms Paper7B4Analytic.mixed_full_p_small_root

theorem full_p_mixed_nonintegral (p q : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (hq : ∃ i, 0 < q i) : ¬ IsIntegralGraph (SG 4 p q) := by
  intro hG
  obtain ⟨t,ht0,ht1,hft⟩ := mixed_full_p_small_root p q hp hq
  let s : ℝ := Real.sqrt t
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
  have hsq : s^2 = t := Real.sq_sqrt ht0.le
  have hs1 : s < 1 := by nlinarith only [hsq,ht1,sq_nonneg (s-1)]
  have hpoly : mixedPolynomial p q (s^2) = 0 := by rw [hsq]; exact hft
  have hmem := (mixed_ordinary_spec_iff p q s (by linarith) (by linarith)
    (by linarith)).mpr hpoly
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p q) hG s hmem
  have hz0 : (0 : ℤ) < z := by rw [hz] at hs0; exact_mod_cast hs0
  have hz1 : z < (1 : ℤ) := by rw [hz] at hs1; exact_mod_cast hs1
  omega
#print axioms Paper7B4Analytic.full_p_mixed_nonintegral

theorem full_p_mixed_sum_nonintegral (p q : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (hq : 0 < ∑ i, q i) : ¬ IsIntegralGraph (SG 4 p q) := by
  apply full_p_mixed_nonintegral p q hp
  by_contra hh
  push Not at hh
  have hz : q = (fun _ => 0) := by funext i; have hi := hh i; omega
  rw [hz] at hq
  simp at hq
#print axioms Paper7B4Analytic.full_p_mixed_sum_nonintegral

end Paper7B4Analytic
