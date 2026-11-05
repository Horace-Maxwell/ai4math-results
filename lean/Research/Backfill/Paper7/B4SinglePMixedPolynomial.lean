import Research.Backfill.Paper7.B4FullPMixedExclusion

/-! Source-only reduction of a single P site with arbitrary Q to a scalar
polynomial. All roots used are strictly inside the genuine spectral gap (0,1). -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

def singlePMixedPolynomial (a u v w z t : ℝ) : ℝ :=
  t*(t^2-(a+u+1)*t+a)*(t-v-1)*(t-w-1)*(t-z-1)-
    (t-1)^2*((t^2-(a+u+1)*t+a)+t*(t-w-1))*(2*t-v-z-2)
#print axioms Paper7B4Analytic.singlePMixedPolynomial

def singlePDisjointPolynomial (a s b c t : ℝ) : ℝ :=
  t*(t-1)*(t-a)*(t-c-1)*(t^2-(s+2)*t+b+s+1)-
    (t-1)^2*((t-1)*(t-a)+t*(t-c-1))*(2*t-s-2)
#print axioms Paper7B4Analytic.singlePDisjointPolynomial

theorem single_p_mixed_factor (p q : Fin 4 → ℕ)
    (hp1 : p 1 = 0) (hp2 : p 2 = 0) (hp3 : p 3 = 0) (t : ℝ) :
    mixedPolynomial p q t = t^2*singlePMixedPolynomial (p 0) (q 0) (q 1) (q 2) (q 3) t := by
  unfold mixedPolynomial mixedLocalPolynomial singlePMixedPolynomial
  rw [hp1,hp2,hp3]
  norm_num
  ring
#print axioms Paper7B4Analytic.single_p_mixed_factor

theorem single_p_disjoint_factor (a v w z t : ℝ) :
    singlePMixedPolynomial a 0 v w z t = singlePDisjointPolynomial a (v+z) (v*z) w t := by
  unfold singlePMixedPolynomial singlePDisjointPolynomial
  ring
#print axioms Paper7B4Analytic.single_p_disjoint_factor

theorem open_unit_root_of_factor (F f : ℝ → ℝ) (hf : Continuous f)
    (hsign : (f 0 < 0 ∧ 0 < f 1) ∨ (0 < f 0 ∧ f 1 < 0))
    (hfac : ∀ t : ℝ, f t = 0 → F t = 0) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ F t = 0 := by
  rcases hsign with h | h
  · obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
      hf.continuousOn h
    exact ⟨t,ht.1,ht.2,hfac t hft⟩
  · have hneg : Continuous (fun t : ℝ => -f t) := hf.neg
    have hzero : (0 : ℝ) ∈ Set.Ioo (-f 0) (-f 1) := ⟨by linarith [h.1],by linarith [h.2]⟩
    obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
      hneg.continuousOn hzero
    have hz : f t = 0 := by linarith only [hft]
    exact ⟨t,ht.1,ht.2,hfac t hz⟩
#print axioms Paper7B4Analytic.open_unit_root_of_factor

theorem mixed_small_root_nonintegral (p q : Fin 4 → ℕ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (he : mixedPolynomial p q t = 0) :
    ¬ IsIntegralGraph (SG 4 p q) := by
  intro hG
  let s : ℝ := Real.sqrt t
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
  have hsq : s^2 = t := Real.sq_sqrt ht0.le
  have hs1 : s < 1 := by nlinarith
  have hpoly : mixedPolynomial p q (s^2) = 0 := by rw [hsq]; exact he
  have hmem := (mixed_ordinary_spec_iff p q s (by linarith) (by linarith)
    (by linarith)).mpr hpoly
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry _ hG s hmem
  rw [hz] at hs0 hs1
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hs0
  have hz1 : z < (1 : ℤ) := by exact_mod_cast hs1
  omega
#print axioms Paper7B4Analytic.mixed_small_root_nonintegral

end Paper7B4Analytic
