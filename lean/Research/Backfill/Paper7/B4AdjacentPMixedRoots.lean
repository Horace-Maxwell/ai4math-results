import Research.Backfill.Paper7.B4AdjacentPMixedPolynomial

/-! Source-only open-unit root for adjacent positive P sites and nonzero Q.
The auxiliary roots are chosen before the vertex of each quadratic. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open scoped BigOperators

theorem adjacent_local_antitone (a q : ℕ) (ha : 0 < a) (x y : ℝ)
    (hxy : x ≤ y) (hy1 : y ≤ 1) (hya : a = 1 → y ≤ 1/2) :
    adjacentLocalPolynomial a q y ≤ adjacentLocalPolynomial a q x := by
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hcoef : 0 ≤ (a : ℝ)+q+2-2*x-2*y := by
    by_cases ha1 : a = 1
    · have hyhalf := hya ha1
      have haR : (a : ℝ) = 1 := by exact_mod_cast ha1
      linarith only [hxy,hyhalf,haR,hqR]
    · have haR : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
      linarith only [hxy,hy1,haR,hqR]
  have hprod := mul_nonneg (sub_nonneg.mpr hxy) hcoef
  unfold adjacentLocalPolynomial
  nlinarith only [hprod]
#print axioms Paper7B4Analytic.adjacent_local_antitone

theorem adjacent_local_small_root (a q : ℕ) (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (a = 1 → r ≤ 1/2) ∧
      adjacentLocalPolynomial a q r = 0 ∧ (0 < q → r < 1) := by
  have h0 : adjacentLocalPolynomial a q 0 = (a : ℝ) := by
    unfold adjacentLocalPolynomial
    ring
  by_cases ha1 : a = 1
  · subst a
    have hhalf : adjacentLocalPolynomial 1 q (1/2) = -(q : ℝ)/2 := by
      unfold adjacentLocalPolynomial
      ring
    by_cases hq0 : q = 0
    · refine ⟨1/2,by norm_num,by norm_num,fun _ => le_rfl,?_,?_⟩
      · simpa only [hq0,Nat.cast_zero,neg_zero,zero_div] using hhalf
      · intro hq
        omega
    have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero hq0)
    let f : ℝ → ℝ := fun t => -adjacentLocalPolynomial 1 q t
    have hcont : Continuous f := by dsimp [f,adjacentLocalPolynomial]; fun_prop
    have hzero : (0 : ℝ) ∈ Set.Ioo (f 0) (f (1/2)) := by
      dsimp [f]
      rw [h0,hhalf,Nat.cast_one]
      constructor <;> linarith
    obtain ⟨r,hr,hfr⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1/2)
      hcont.continuousOn hzero
    have hAr : adjacentLocalPolynomial 1 q r = 0 := by
      change -adjacentLocalPolynomial 1 q r = 0 at hfr
      linarith only [hfr]
    exact ⟨r,hr.1,by linarith [hr.2],fun _ => hr.2.le,hAr,fun _ => by linarith [hr.2]⟩
  have h1 : adjacentLocalPolynomial a q 1 = -(q : ℝ) := by
    unfold adjacentLocalPolynomial
    ring
  by_cases hq0 : q = 0
  · refine ⟨1,by norm_num,le_rfl,?_,?_,?_⟩
    · intro hh
      exact False.elim (ha1 hh)
    · simpa only [hq0,Nat.cast_zero,neg_zero] using h1
    · intro hq
      omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hqR : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero hq0)
  let f : ℝ → ℝ := fun t => -adjacentLocalPolynomial a q t
  have hcont : Continuous f := by dsimp [f,adjacentLocalPolynomial]; fun_prop
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 0) (f 1) := by
    dsimp [f]
    rw [h0,h1]
    constructor <;> linarith
  obtain ⟨r,hr,hfr⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzero
  have hAr : adjacentLocalPolynomial a q r = 0 := by
    change -adjacentLocalPolynomial a q r = 0 at hfr
    linarith only [hfr]
  exact ⟨r,hr.1,hr.2.le,fun hh => False.elim (ha1 hh),hAr,fun _ => hr.2⟩
#print axioms Paper7B4Analytic.adjacent_local_small_root

theorem adjacent_two_p_test_point (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hq : 0 < ∑ i, q i) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 0 < adjacentPMixedPolynomial p q r := by
  obtain ⟨s0,hs00,hs01,hs0a,hs0E,hs0strict⟩ :=
    adjacent_local_small_root (p 0) (q 0+q 2) hp0
  obtain ⟨s1,hs10,hs11,hs1a,hs1E,hs1strict⟩ :=
    adjacent_local_small_root (p 1) (q 1+q 3) hp1
  let r : ℝ := min s0 s1
  have hr0 : 0 < r := lt_min hs00 hs10
  have hrle0 : r ≤ s0 := min_le_left _ _
  have hrle1 : r ≤ s1 := min_le_right _ _
  have hr1 : r < 1 := by
    have hqcases : 0 < q 0+q 2 ∨ 0 < q 1+q 3 := by
      rw [Fin.sum_univ_four] at hq
      omega
    rcases hqcases with h02 | h13
    · exact hrle0.trans_lt (hs0strict h02)
    · exact hrle1.trans_lt (hs1strict h13)
  have hE0 : 0 ≤ adjacentLocalPolynomial (p 0) (q 0+q 2) r := by
    have hh := adjacent_local_antitone (p 0) (q 0+q 2) hp0 r s0 hrle0 hs01 hs0a
    rw [hs0E] at hh
    exact hh
  have hE1 : 0 ≤ adjacentLocalPolynomial (p 1) (q 1+q 3) r := by
    have hh := adjacent_local_antitone (p 1) (q 1+q 3) hp1 r s1 hrle1 hs11 hs1a
    rw [hs1E] at hh
    exact hh
  have hzero : adjacentLocalPolynomial (p 0) (q 0+q 2) r = 0 ∨
      adjacentLocalPolynomial (p 1) (q 1+q 3) r = 0 := by
    rcases min_choice s0 s1 with hh | hh
    · left
      change adjacentLocalPolynomial (p 0) (q 0+q 2) (min s0 s1) = 0
      rw [hh]
      exact hs0E
    · right
      change adjacentLocalPolynomial (p 1) (q 1+q 3) (min s0 s1) = 0
      rw [hh]
      exact hs1E
  have hD2 : r-(q 2 : ℝ)-1 < 0 := by
    have hh : (0 : ℝ) ≤ q 2 := Nat.cast_nonneg _
    linarith only [hr1,hh]
  have hD3 : r-(q 3 : ℝ)-1 < 0 := by
    have hh : (0 : ℝ) ≤ q 3 := Nat.cast_nonneg _
    linarith only [hr1,hh]
  have hA0 : 0 < mixedLocalPolynomial (p 0) (q 0) r := by
    rw [← adjacent_p_pair_zero p q r] at hE0
    have hh := mul_neg_of_pos_of_neg hr0 hD2
    linarith only [hE0,hh]
  have hA1 : 0 < mixedLocalPolynomial (p 1) (q 1) r := by
    rw [← adjacent_p_pair_one p q r] at hE1
    have hh := mul_neg_of_pos_of_neg hr0 hD3
    linarith only [hE1,hh]
  have hEprod : (mixedLocalPolynomial (p 0) (q 0) r+r*(r-q 2-1))*
      (mixedLocalPolynomial (p 1) (q 1) r+r*(r-q 3-1)) = 0 := by
    rw [adjacent_p_pair_zero,adjacent_p_pair_one]
    rcases hzero with hh | hh <;> simp only [hh,zero_mul,mul_zero]
  have hprod : 0 < r*mixedLocalPolynomial (p 0) (q 0) r*
      mixedLocalPolynomial (p 1) (q 1) r*(r-q 2-1)*(r-q 3-1) :=
    mul_pos_of_neg_of_neg
      (mul_neg_of_pos_of_neg (mul_pos (mul_pos hr0 hA0) hA1) hD2) hD3
  refine ⟨r,hr0,hr1,?_⟩
  unfold adjacentPMixedPolynomial
  rw [hEprod,mul_zero,sub_zero]
  exact hprod
#print axioms Paper7B4Analytic.adjacent_two_p_test_point

theorem adjacent_two_p_small_root (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hq : 0 < ∑ i, q i) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ adjacentPMixedPolynomial p q t = 0 := by
  obtain ⟨r,hr0,hr1,hHr⟩ := adjacent_two_p_test_point p q hp0 hp1 hq
  have hH0eq : adjacentPMixedPolynomial p q 0 = -(p 0 : ℝ)*p 1 := by
    unfold adjacentPMixedPolynomial mixedLocalPolynomial
    ring
  have hH0 : adjacentPMixedPolynomial p q 0 < 0 := by
    have hp0R : (0 : ℝ) < p 0 := by exact_mod_cast hp0
    have hp1R : (0 : ℝ) < p 1 := by exact_mod_cast hp1
    rw [hH0eq]
    exact mul_neg_of_neg_of_pos (by linarith only [hp0R]) hp1R
  have hcont : Continuous (adjacentPMixedPolynomial p q) := by
    unfold adjacentPMixedPolynomial mixedLocalPolynomial
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Ioo (adjacentPMixedPolynomial p q 0)
      (adjacentPMixedPolynomial p q r) := ⟨hH0,hHr⟩
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo hr0.le hcont.continuousOn hzero
  exact ⟨t,ht.1,ht.2.trans hr1,hft⟩
#print axioms Paper7B4Analytic.adjacent_two_p_small_root

end Paper7B4Analytic
