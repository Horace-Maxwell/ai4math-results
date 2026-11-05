import Research.Backfill.Paper7.B4AdjacentPMixedRoots
import Research.Backfill.Paper7.B4SinglePMixedPolynomial

/-! Source-only exclusion of Q meeting the three positive P sites. The
minimum of a pair-sum root and the middle-site root gives an open-unit root. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def threePMixedPolynomial (p q : Fin 4 → ℕ) (t : ℝ) : ℝ :=
  mixedLocalPolynomial (p 0) (q 0) t*mixedLocalPolynomial (p 1) (q 1) t*
    mixedLocalPolynomial (p 2) (q 2) t*(t-q 3-1)-
  (t-1)^2*(mixedLocalPolynomial (p 0) (q 0) t+mixedLocalPolynomial (p 2) (q 2) t)*
    (mixedLocalPolynomial (p 1) (q 1) t+t*(t-q 3-1))
#print axioms Paper7B4Analytic.threePMixedPolynomial

theorem three_p_mixed_factor (p q : Fin 4 → ℕ) (hp3 : p 3 = 0) (t : ℝ) :
    mixedPolynomial p q t = t*threePMixedPolynomial p q t := by
  unfold mixedPolynomial threePMixedPolynomial mixedLocalPolynomial
  rw [hp3]
  norm_num
  ring
#print axioms Paper7B4Analytic.three_p_mixed_factor

theorem three_p_opposite_sum (p q : Fin 4 → ℕ) (t : ℝ) :
    mixedLocalPolynomial (p 0) (q 0) t+mixedLocalPolynomial (p 2) (q 2) t =
      adjacentLocalPolynomial (p 0+p 2) (q 0+q 2) t := by
  unfold mixedLocalPolynomial adjacentLocalPolynomial
  push_cast
  ring
#print axioms Paper7B4Analytic.three_p_opposite_sum

theorem three_p_overlap_test_point (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2)
    (hq : 0 < q 0+q 1+q 2) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 0 ≤ threePMixedPolynomial p q r := by
  have hpsum : 0 < p 0+p 2 := by omega
  obtain ⟨s,hs0,hs1,hsa,hsE,hsstrict⟩ :=
    adjacent_local_small_root (p 0+p 2) (q 0+q 2) hpsum
  obtain ⟨u,hu0,hu1,huA,hustrict⟩ := mixed_local_small_root (p 1) (q 1) hp1
  let r : ℝ := min s u
  have hr0 : 0 < r := lt_min hs0 hu0
  have hrs : r ≤ s := min_le_left _ _
  have hru : r ≤ u := min_le_right _ _
  have hr1 : r < 1 := by
    have hcases : 0 < q 0+q 2 ∨ 0 < q 1 := by omega
    rcases hcases with h02 | h1
    · exact hrs.trans_lt (hsstrict h02)
    · exact hru.trans_lt (hustrict h1)
  have hS : 0 ≤ mixedLocalPolynomial (p 0) (q 0) r+mixedLocalPolynomial (p 2) (q 2) r := by
    rw [three_p_opposite_sum]
    have hh := adjacent_local_antitone (p 0+p 2) (q 0+q 2) hpsum r s hrs hs1 hsa
    rw [hsE] at hh
    exact hh
  have hA1 : 0 ≤ mixedLocalPolynomial (p 1) (q 1) r := by
    have hh := mixed_local_antitone (p 1) (q 1) hp1 r u hru hu1
    rw [huA] at hh
    exact hh
  have hD : r-(q 3 : ℝ)-1 < 0 := by
    have hh : (0 : ℝ) ≤ q 3 := Nat.cast_nonneg _
    linarith
  have hzero : mixedLocalPolynomial (p 0) (q 0) r+mixedLocalPolynomial (p 2) (q 2) r = 0 ∨
      mixedLocalPolynomial (p 1) (q 1) r = 0 := by
    rcases min_choice s u with hh | hh
    · left
      rw [three_p_opposite_sum]
      change adjacentLocalPolynomial (p 0+p 2) (q 0+q 2) (min s u) = 0
      rw [hh]
      exact hsE
    · right
      change mixedLocalPolynomial (p 1) (q 1) (min s u) = 0
      rw [hh]
      exact huA
  refine ⟨r,hr0,hr1,?_⟩
  rcases hzero with hSz | hAz
  · have hpair : mixedLocalPolynomial (p 0) (q 0) r*
        mixedLocalPolynomial (p 2) (q 2) r ≤ 0 := by
      have hh : mixedLocalPolynomial (p 2) (q 2) r = -mixedLocalPolynomial (p 0) (q 0) r :=
        by linarith only [hSz]
      rw [hh]
      nlinarith only [sq_nonneg (mixedLocalPolynomial (p 0) (q 0) r)]
    have hleft : mixedLocalPolynomial (p 0) (q 0) r*mixedLocalPolynomial (p 1) (q 1) r*
        mixedLocalPolynomial (p 2) (q 2) r ≤ 0 := by
      have hh := mul_nonpos_of_nonpos_of_nonneg hpair hA1
      nlinarith only [hh]
    have hprod := mul_nonneg_of_nonpos_of_nonpos hleft hD.le
    unfold threePMixedPolynomial
    rw [hSz,mul_zero,zero_mul,sub_zero]
    exact hprod
  · have hscale : 0 ≤ (r-1)^2*(mixedLocalPolynomial (p 0) (q 0) r+
        mixedLocalPolynomial (p 2) (q 2) r) := mul_nonneg (sq_nonneg _) hS
    have hright : r*(r-(q 3 : ℝ)-1) ≤ 0 := (mul_neg_of_pos_of_neg hr0 hD).le
    have hprod := mul_nonpos_of_nonneg_of_nonpos hscale hright
    unfold threePMixedPolynomial
    simp only [hAz,mul_zero,zero_mul,zero_add]
    linarith only [hprod]
#print axioms Paper7B4Analytic.three_p_overlap_test_point

theorem three_p_overlap_nonintegral (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hq : 0 < q 0+q 1+q 2) : ¬ IsIntegralGraph (SG 4 p q) := by
  obtain ⟨r,hr0,hr1,hHr⟩ := three_p_overlap_test_point p q hp0 hp1 hp2 hq
  have hH0eq : threePMixedPolynomial p q 0 =
      -(p 1 : ℝ)*((p 0 : ℝ)*p 2*((q 3 : ℝ)+1)+p 0+p 2) := by
    unfold threePMixedPolynomial mixedLocalPolynomial
    ring
  have hp0R : (0 : ℝ) < p 0 := by exact_mod_cast hp0
  have hp1R : (0 : ℝ) < p 1 := by exact_mod_cast hp1
  have hp2R : (0 : ℝ) < p 2 := by exact_mod_cast hp2
  have hH0 : threePMixedPolynomial p q 0 < 0 := by
    rw [hH0eq]
    apply mul_neg_of_neg_of_pos (by linarith)
    positivity
  have hcont : Continuous (threePMixedPolynomial p q) := by
    unfold threePMixedPolynomial mixedLocalPolynomial
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (threePMixedPolynomial p q 0) (threePMixedPolynomial p q r) :=
    ⟨hH0.le,hHr⟩
  obtain ⟨t,ht,hHt⟩ := intermediate_value_Icc hr0.le hcont.continuousOn hzero
  have ht0 : 0 < t := by
    by_contra hh
    have htz : t = 0 := by linarith [ht.1]
    rw [htz] at hHt
    linarith
  have hFt : mixedPolynomial p q t = 0 := by rw [three_p_mixed_factor p q hp3 t,hHt,mul_zero]
  exact mixed_small_root_nonintegral p q t ht0 (ht.2.trans_lt hr1) hFt
#print axioms Paper7B4Analytic.three_p_overlap_nonintegral

theorem three_p_integral_q_disjoint (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hG : IsIntegralGraph (SG 4 p q)) : q 0 = 0 ∧ q 1 = 0 ∧ q 2 = 0 := by
  have hnot : ¬ 0 < q 0+q 1+q 2 := by
    intro hh
    exact three_p_overlap_nonintegral p q hp0 hp1 hp2 hp3 hh hG
  omega
#print axioms Paper7B4Analytic.three_p_integral_q_disjoint

end Paper7B4Analytic
