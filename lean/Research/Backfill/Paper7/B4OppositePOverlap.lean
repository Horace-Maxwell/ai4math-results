import Research.Backfill.Paper7.B4OppositePMixedPolynomial

/-! Source-only exclusion of Q meeting either of the two positive P sites. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge

theorem opposite_p_single_overlap_small_root (a c u s b : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hu : 0 < u) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ oppositePMixedPolynomial a c u 0 s b t = 0 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  by_cases hb0 : b = 0
  · subst b
    by_cases hs0 : s = 0
    · subst s
      let f : ℝ → ℝ := fun t => mixedLocalPolynomial a u t*(t-c-2)-2*(t-1)*(t-c)
      have hcont : Continuous f := by dsimp [f,mixedLocalPolynomial]; fun_prop
      have h0 : f 0 = -(a : ℝ)*c-2*a-2*c := by dsimp [f,mixedLocalPolynomial]; ring
      have h1 : f 1 = (u : ℝ)*((c : ℝ)+1) := by dsimp [f,mixedLocalPolynomial]; ring
      apply open_unit_root_of_factor (oppositePMixedPolynomial a c u 0 0 0) f hcont
        (Or.inl ⟨by rw [h0]; nlinarith only [haR,hcR,mul_pos haR hcR],
          by rw [h1]; exact mul_pos huR (by linarith)⟩)
      intro t hf
      have he : oppositePMixedPolynomial a c u 0 0 0 t = (t-1)^3*f t := by
        dsimp [oppositePMixedPolynomial,f,mixedLocalPolynomial]
        ring
      rw [he,hf,mul_zero]
    have hspos : (0 : ℝ) < s := by exact_mod_cast (Nat.pos_of_ne_zero hs0)
    let f : ℝ → ℝ := fun t => mixedLocalPolynomial a u t*(t-c)*(t-s-1)-
      (mixedLocalPolynomial a u t+(t-1)*(t-c))*(2*t-s-2)
    have hcont : Continuous f := by dsimp [f,mixedLocalPolynomial]; fun_prop
    have h0 : f 0 = (a : ℝ)*c*((s : ℝ)+1)+((a : ℝ)+c)*((s : ℝ)+2) := by
      dsimp [f,mixedLocalPolynomial]; ring
    have h1 : f 1 = -(u : ℝ)*c*s := by dsimp [f,mixedLocalPolynomial]; ring
    apply open_unit_root_of_factor (oppositePMixedPolynomial a c u 0 s 0) f hcont
      (Or.inr ⟨by rw [h0]; positivity,
        by rw [h1]; nlinarith only [mul_pos (mul_pos huR hcR) hspos]⟩)
    intro t hf
    have he : oppositePMixedPolynomial a c u 0 s 0 t = (t-1)^2*f t := by
      dsimp [oppositePMixedPolynomial,f,mixedLocalPolynomial]
      ring
    rw [he,hf,mul_zero]
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (Nat.pos_of_ne_zero hb0)
  by_cases hc1 : c = 1
  · subst c
    let f : ℝ → ℝ := fun t => mixedLocalPolynomial a u t*(t^2-((s : ℝ)+2)*t+b+s+1)-
      (mixedLocalPolynomial a u t+(t-1)^2)*(2*t-s-2)
    have hcont : Continuous f := by dsimp [f,mixedLocalPolynomial]; fun_prop
    have h0 : f 0 = (a : ℝ)*((b : ℝ)+s+1)+((a : ℝ)+1)*((s : ℝ)+2) := by
      dsimp [f,mixedLocalPolynomial]; ring
    have h1 : f 1 = -(u : ℝ)*((b : ℝ)+s) := by dsimp [f,mixedLocalPolynomial]; ring
    apply open_unit_root_of_factor (oppositePMixedPolynomial a 1 u 0 s b) f hcont
      (Or.inr ⟨by rw [h0]; positivity,
        by rw [h1]; exact mul_neg_of_neg_of_pos (by linarith) (by linarith)⟩)
    intro t hf
    have he : oppositePMixedPolynomial a 1 u 0 s b t = (t-1)^2*f t := by
      dsimp [oppositePMixedPolynomial,f,mixedLocalPolynomial]
      ring
    rw [he,hf,mul_zero]
  have hc2 : (1 : ℝ) < c := by exact_mod_cast (show 1 < c by omega)
  let f : ℝ → ℝ := fun t => mixedLocalPolynomial a u t*(t-c)*
    (t^2-((s : ℝ)+2)*t+b+s+1)-
    (t-1)*(mixedLocalPolynomial a u t+(t-1)*(t-c))*(2*t-s-2)
  have hcont : Continuous f := by dsimp [f,mixedLocalPolynomial]; fun_prop
  have h0 : f 0 = -(a : ℝ)*c*((b : ℝ)+s+1)-((a : ℝ)+c)*((s : ℝ)+2) := by
    dsimp [f,mixedLocalPolynomial]; ring
  have h1 : f 1 = (u : ℝ)*((c : ℝ)-1)*b := by dsimp [f,mixedLocalPolynomial]; ring
  apply open_unit_root_of_factor (oppositePMixedPolynomial a c u 0 s b) f hcont
    (Or.inl ⟨by
      rw [h0]
      have hh : 0 < (a : ℝ)*c*((b : ℝ)+s+1)+((a : ℝ)+c)*((s : ℝ)+2) := by
        positivity
      linarith,
      by rw [h1]; exact mul_pos (mul_pos huR (by linarith)) hbpos⟩)
  intro t hf
  have he : oppositePMixedPolynomial a c u 0 s b t = (t-1)*f t := by
    dsimp [oppositePMixedPolynomial,f,mixedLocalPolynomial]
    ring
  rw [he,hf,mul_zero]
#print axioms Paper7B4Analytic.opposite_p_single_overlap_small_root

theorem opposite_p_double_overlap_small_root (a c u v s b : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hu : 0 < u) (hv : 0 < v) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ oppositePMixedPolynomial a c u v s b t = 0 := by
  obtain ⟨x,hx0,_hxle,hAx,hxs⟩ := mixed_local_small_root a u ha
  obtain ⟨y,hy0,_hyle,hCy,hys⟩ := mixed_local_small_root c v hc
  have hx1 : x < 1 := hxs hu
  have hy1 : y < 1 := hys hv
  let r : ℝ := max x y
  have hr0 : 0 < r := hx0.trans_le (le_max_left _ _)
  have hr1 : r < 1 := max_lt hx1 hy1
  have hAr : mixedLocalPolynomial a u r ≤ 0 := by
    have hh := mixed_local_antitone a u ha x r (le_max_left _ _) hr1.le
    rw [hAx] at hh
    exact hh
  have hCr : mixedLocalPolynomial c v r ≤ 0 := by
    have hh := mixed_local_antitone c v hc y r (le_max_right _ _) hr1.le
    rw [hCy] at hh
    exact hh
  have hprod : mixedLocalPolynomial a u r*mixedLocalPolynomial c v r = 0 := by
    rcases max_choice x y with hh | hh
    · change mixedLocalPolynomial a u (max x y)*mixedLocalPolynomial c v (max x y) = 0
      rw [hh,hAx,zero_mul]
    · change mixedLocalPolynomial a u (max x y)*mixedLocalPolynomial c v (max x y) = 0
      rw [hh,hCy,mul_zero]
  have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hE : 2*r-(s : ℝ)-2 < 0 := by linarith
  have hterm : 0 ≤ (r-1)^2*(mixedLocalPolynomial a u r+mixedLocalPolynomial c v r)*
      (2*r-(s : ℝ)-2) :=
    mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (add_nonpos hAr hCr)) hE.le
  have hHr : oppositePMixedPolynomial a c u v s b r ≤ 0 := by
    unfold oppositePMixedPolynomial
    rw [hprod,zero_mul]
    linarith only [hterm]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hH0 : 0 < oppositePMixedPolynomial a c u v s b 0 := by
    rw [opposite_p_poly_zero]
    positivity
  have hcont : Continuous (oppositePMixedPolynomial a c u v s b) := by
    unfold oppositePMixedPolynomial mixedLocalPolynomial
    fun_prop
  have hzero : (0 : ℝ) ∈ Set.Icc (oppositePMixedPolynomial a c u v s b r)
      (oppositePMixedPolynomial a c u v s b 0) := ⟨hHr,hH0.le⟩
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc' hr0.le hcont.continuousOn hzero
  have ht0 : 0 < t := by
    by_contra hh
    have ht0 : t = 0 := by linarith [ht.1]
    rw [ht0] at hft
    linarith
  exact ⟨t,ht0,ht.2.trans_lt hr1,hft⟩
#print axioms Paper7B4Analytic.opposite_p_double_overlap_small_root

theorem opposite_p_overlap_nonintegral (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : p 1 = 0) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hq : 0 < q 0 ∨ 0 < q 2) : ¬ IsIntegralGraph (SG 4 p q) := by
  have hex : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      oppositePMixedPolynomial (p 0) (p 2) (q 0) (q 2) (q 1+q 3) (q 1*q 3) t = 0 := by
    by_cases hq0 : q 0 = 0
    · have hq2 : 0 < q 2 := by omega
      obtain ⟨t,ht0,ht1,hft⟩ := opposite_p_single_overlap_small_root (p 2) (p 0)
        (q 2) (q 1+q 3) (q 1*q 3) hp2 hp0 hq2
      refine ⟨t,ht0,ht1,?_⟩
      rw [opposite_p_poly_swap,hq0]
      exact hft
    · have hq0p : 0 < q 0 := Nat.pos_of_ne_zero hq0
      by_cases hq2 : q 2 = 0
      · rw [hq2]
        exact opposite_p_single_overlap_small_root (p 0) (p 2) (q 0)
          (q 1+q 3) (q 1*q 3) hp0 hp2 hq0p
      · exact opposite_p_double_overlap_small_root (p 0) (p 2) (q 0) (q 2)
          (q 1+q 3) (q 1*q 3) hp0 hp2 hq0p (Nat.pos_of_ne_zero hq2)
  obtain ⟨t,ht0,ht1,hft⟩ := hex
  have he : mixedPolynomial p q t = 0 := by rw [opposite_p_mixed_factor p q hp1 hp3 t,hft,mul_zero]
  exact mixed_small_root_nonintegral p q t ht0 ht1 he
#print axioms Paper7B4Analytic.opposite_p_overlap_nonintegral

theorem opposite_p_integral_q_disjoint (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : p 1 = 0) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hG : IsIntegralGraph (SG 4 p q)) : q 0 = 0 ∧ q 2 = 0 := by
  have hh : ¬ (0 < q 0 ∨ 0 < q 2) := by
    intro hq
    exact opposite_p_overlap_nonintegral p q hp0 hp1 hp2 hp3 hq hG
  omega
#print axioms Paper7B4Analytic.opposite_p_integral_q_disjoint

end Paper7B4Analytic
