import Research.Backfill.Paper7.B4QOppositeRoots

/-! Source-only exclusion of all nonempty pure-q opposite support, by roots
in open intervals between consecutive integers. No order bound is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem qopposite_two_positive_nonintegral (q : Fin 4 → ℕ)
    (hq0 : 0 < q 0) (hq2 : 0 < q 2) (hq1 : q 1 = 0) (hq3 : q 3 = 0) :
    ¬ IsIntegralGraph (SG 4 (fun _ => 0) q) := by
  intro hG
  let f : ℝ → ℝ := qoppositeCubic (q 0) (q 2)
  have hcont : Continuous f := by
    change Continuous (fun t : ℝ => t^3-((q 0 : ℝ)+q 2+6)*t^2+
      ((q 0 : ℝ)*q 2+3*q 0+3*q 2+9)*t-2*q 0-2*q 2-4)
    fun_prop
  have hf0 : f 0 = -2*(q 0 : ℝ)-2*(q 2 : ℝ)-4 := by
    dsimp [f,qoppositeCubic]
    ring
  have hf1 : f 1 = (q 0 : ℝ)*q 2 := by dsimp [f,qoppositeCubic]; ring
  have hprod : 0 < (q 0 : ℝ)*q 2 :=
    mul_pos (by exact_mod_cast hq0) (by exact_mod_cast hq2)
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 0) (f 1) := by
    rw [hf0,hf1]
    constructor
    · have h0 : (0 : ℝ) ≤ q 0 := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ q 2 := Nat.cast_nonneg _
      linarith only [h0,h2]
    · exact hprod
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzero
  let s : ℝ := Real.sqrt t
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht.1
  have hsq : s^2 = t := Real.sq_sqrt ht.1.le
  have hs1 : s < 1 := by nlinarith [ht.2]
  have hpoly : qoppositeCubic (q 0) (q 2) (s^2) = 0 := by rw [hsq]; exact hft
  have hmem := (qopposite_ordinary_spec_iff q hq1 hq3 s
    (by linarith) (by linarith) (by linarith)).mpr hpoly
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 (fun _ => 0) q) hG s hmem
  have hz0 : (0 : ℤ) < z := by rw [hz] at hs0; exact_mod_cast hs0
  have hz1 : z < (1 : ℤ) := by rw [hz] at hs1; exact_mod_cast hs1
  omega
#print axioms Paper7B4Analytic.qopposite_two_positive_nonintegral

theorem qopposite_single_nonintegral (q : Fin 4 → ℕ)
    (hpos : 0 < q 0+q 2) (hab : q 0*q 2 = 0)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0) :
    ¬ IsIntegralGraph (SG 4 (fun _ => 0) q) := by
  intro hG
  have hposR : (0 : ℝ) < (q 0 : ℝ)+q 2 := by exact_mod_cast hpos
  have habR : (q 0 : ℝ)*q 2 = 0 := by exact_mod_cast hab
  let f : ℝ → ℝ := fun t => -(t^2-((q 0 : ℝ)+q 2+5)*t+2*(q 0 : ℝ)+2*(q 2 : ℝ)+4)
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hf1 : f 1 = -((q 0 : ℝ)+q 2) := by dsimp [f]; ring
  have hf2 : f 2 = 2 := by dsimp [f]; ring
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 1) (f 2) := by
    rw [hf1,hf2]
    exact ⟨by linarith only [hposR],by norm_num⟩
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2)
    hcont.continuousOn hzero
  let s : ℝ := Real.sqrt t
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hsq : s^2 = t := Real.sq_sqrt (by linarith [ht.1])
  have hs1 : 1 < s := by nlinarith [ht.1]
  have hs2 : s < 2 := by nlinarith [ht.2]
  have hquad : t^2-((q 0 : ℝ)+q 2+5)*t+2*(q 0 : ℝ)+2*(q 2 : ℝ)+4 = 0 := by
    change -(t^2-((q 0 : ℝ)+q 2+5)*t+2*(q 0 : ℝ)+2*(q 2 : ℝ)+4) = 0 at hft
    linarith only [hft]
  have hpoly : qoppositeCubic (q 0) (q 2) (s^2) = 0 := by
    rw [hsq,qopposite_cubic_single_factor _ _ _ habR,hquad,mul_zero]
  have hmem := (qopposite_ordinary_spec_iff q hq1 hq3 s
    (by linarith) (by linarith) (by linarith)).mpr hpoly
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry (SG 4 (fun _ => 0) q) hG s hmem
  have hz1 : (1 : ℤ) < z := by rw [hz] at hs1; exact_mod_cast hs1
  have hz2 : z < (2 : ℤ) := by rw [hz] at hs2; exact_mod_cast hs2
  omega
#print axioms Paper7B4Analytic.qopposite_single_nonintegral

theorem pure_q_opposite_nonintegral (q : Fin 4 → ℕ)
    (hq : 0 < ∑ k, q k) (hq1 : q 1 = 0) (hq3 : q 3 = 0) :
    ¬ IsIntegralGraph (SG 4 (fun _ => 0) q) := by
  have hpos : 0 < q 0+q 2 := by
    simpa only [Fin.sum_univ_four,hq1,hq3,Nat.add_zero] using hq
  by_cases hab : q 0*q 2 = 0
  · exact qopposite_single_nonintegral q hpos hab hq1 hq3
  · have h0 : 0 < q 0 := Nat.pos_of_ne_zero (by intro hz; apply hab; simp [hz])
    have h2 : 0 < q 2 := Nat.pos_of_ne_zero (by intro hz; apply hab; simp [hz])
    exact qopposite_two_positive_nonintegral q h0 h2 hq1 hq3
#print axioms Paper7B4Analytic.pure_q_opposite_nonintegral

end Paper7B4Analytic
