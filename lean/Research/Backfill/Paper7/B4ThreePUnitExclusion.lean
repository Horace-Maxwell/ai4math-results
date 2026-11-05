import Research.Backfill.Paper7.B4QzeroUnitSpectrum
import Research.Backfill.Paper7.B4ThreePSpectral

/-! Source-only exclusion of the exceptional root 1 for three positive P1
sites. The two possible parameter shapes are derived from its equation. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem integral_no_spec_between_one_two (p q : Fin 4 → ℕ)
    (hG : IsIntegralGraph (SG 4 p q)) (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    s ∉ spec (SG 4 p q) := by
  intro hmem
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 p q) hG s hmem
  rw [hz] at hs1 hs2
  have hz1 : (1 : ℤ) < z := by exact_mod_cast hs1
  have hz2 : z < (2 : ℤ) := by exact_mod_cast hs2
  omega
#print axioms Paper7B4Analytic.integral_no_spec_between_one_two

theorem three_p_unit_parameter_shapes (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hunit : 1 ∈ spec (SG 4 p (fun _ => 0))) :
    (p 0 = 1 ∧ p 2 = 1) ∨ (p 1 = 2 ∧ (p 0 = 1 ∨ p 2 = 1)) := by
  let u := p 0-1
  let v := p 2-1
  let w := p 1-1
  have h0 : p 0 = u+1 := by dsimp [u]; omega
  have h2 : p 2 = v+1 := by dsimp [v]; omega
  have h1 : p 1 = w+1 := by dsimp [w]; omega
  have hpoly := (qzero_unit_spec_iff p).mp hunit
  rw [h0,h1,h2,hp3] at hpoly
  push_cast at hpoly
  have heR : (u : ℝ)+v = (w : ℝ)*((u : ℝ)+v+u*v) := by
    unfold qzeroQuartic at hpoly
    nlinarith only [hpoly]
  have he : u+v = w*(u+v+u*v) := by exact_mod_cast heR
  by_cases hz : u+v = 0
  · exact Or.inl ⟨by omega,by omega⟩
  have hwpos : 0 < w := by
    by_contra hh
    have hw0 : w = 0 := by omega
    rw [hw0,zero_mul] at he
    exact hz he
  have hwle : w ≤ 1 := by
    by_contra hh
    have hw2 : 2 ≤ w := by omega
    have hle := Nat.mul_le_mul_right (u+v+u*v) hw2
    nlinarith only [hle,he,show 0 < u+v by omega]
  have hw : w = 1 := by omega
  rw [hw,one_mul] at he
  have huv : u*v = 0 := by omega
  refine Or.inr ⟨by omega,?_⟩
  rcases mul_eq_zero.mp huv with hu | hv
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)
#print axioms Paper7B4Analytic.three_p_unit_parameter_shapes

theorem three_p_quadratic_gap_nonintegral (p : Fin 4 → ℕ) (hp3 : p 3 = 0)
    (A B : ℝ)
    (hfac : ∀ t : ℝ, threePCubic (p 0) (p 1) (p 2) t = (t-1)*(t^2-A*t+B))
    (h1 : 0 < 1-A+B) (h4 : 16-4*A+B < 0) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  let f : ℝ → ℝ := fun t => -(t^2-A*t+B)
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 1) (f 4) := by
    dsimp [f]
    norm_num
    constructor <;> linarith
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 4)
    hcont.continuousOn hzero
  let s : ℝ := Real.sqrt t
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hsq : s^2 = t := Real.sq_sqrt (by linarith [ht.1])
  have hs1 : 1 < s := by nlinarith [ht.1]
  have hs2 : s < 2 := by nlinarith [ht.2]
  have hquad : t^2-A*t+B = 0 := by change -(t^2-A*t+B) = 0 at hft; linarith
  have hpoly : threePCubic (p 0) (p 1) (p 2) (s^2) = 0 := by
    rw [hsq,hfac,hquad,mul_zero]
  have hmem := (three_p_ordinary_spec_iff p hp3 s (by linarith) (by linarith)
    (by linarith)).mpr hpoly
  exact integral_no_spec_between_one_two p (fun _ => 0) hG s hs1 hs2 hmem
#print axioms Paper7B4Analytic.three_p_quadratic_gap_nonintegral

theorem three_p_unit_nonintegral (p : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hunit : 1 ∈ spec (SG 4 p (fun _ => 0))) :
    ¬ IsIntegralGraph (SG 4 p (fun _ => 0)) := by
  intro hG
  have hpend : 0 < ∑ i, p i := by rw [Fin.sum_univ_four]; omega
  rcases three_p_unit_parameter_shapes p hp0 hp1 hp2 hp3 hunit with
    ⟨h0,h2⟩ | ⟨h1,hend⟩
  · by_cases hb : p 1 ≤ 2
    · have hn : nOf 4 p (fun _ => 0) ≤ 8 := by
        simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero,Fin.sum_univ_four]
        omega
      exact qzero_small_order_nonintegral p hpend hn hG
    have hbR : (2 : ℝ) < p 1 := by exact_mod_cast (show 2 < p 1 by omega)
    apply three_p_quadratic_gap_nonintegral p hp3 ((p 1 : ℝ)+5) (3*(p 1 : ℝ))
      (fun t => by rw [h0,h2]; norm_num [threePCubic]; ring) (by linarith) (by linarith) hG
  · rcases hend with h0 | h2
    · by_cases hc : p 2 = 1
      · have hn : nOf 4 p (fun _ => 0) ≤ 8 := by
          simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero,Fin.sum_univ_four]
          omega
        exact qzero_small_order_nonintegral p hpend hn hG
      have hcR : (1 : ℝ) < p 2 := by exact_mod_cast (show 1 < p 2 by omega)
      apply three_p_quadratic_gap_nonintegral p hp3 ((p 2 : ℝ)+6) (4*(p 2 : ℝ)+2)
        (fun t => by rw [h0,h1]; norm_num [threePCubic]; ring) (by linarith) (by linarith) hG
    · by_cases ha : p 0 = 1
      · have hn : nOf 4 p (fun _ => 0) ≤ 8 := by
          simp only [nOf,Finset.sum_const_zero,mul_zero,add_zero,Fin.sum_univ_four]
          omega
        exact qzero_small_order_nonintegral p hpend hn hG
      have haR : (1 : ℝ) < p 0 := by exact_mod_cast (show 1 < p 0 by omega)
      apply three_p_quadratic_gap_nonintegral p hp3 ((p 0 : ℝ)+6) (4*(p 0 : ℝ)+2)
        (fun t => by rw [h1,h2]; norm_num [threePCubic]; ring) (by linarith) (by linarith) hG
#print axioms Paper7B4Analytic.three_p_unit_nonintegral

end Paper7B4Analytic
