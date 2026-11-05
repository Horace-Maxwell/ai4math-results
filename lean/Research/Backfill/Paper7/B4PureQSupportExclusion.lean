import Research.Backfill.Paper7.B4PureQPolynomial
import Research.Backfill.Paper7.B4OppositeBranch

/-! Source-only full exclusions of three or four positive Q sites with P=0.
No order bound is needed for these support shapes. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem pure_q_four_positive_nonintegral (q : Fin 4 → ℕ) (hq : ∀ i, 0 < q i) :
    ¬ IsIntegralGraph (SG 4 (fun _ => 0) q) := by
  let f : ℝ → ℝ := pureQPolynomial (q 0) (q 1) (q 2) (q 3)
  have hcont : Continuous f := by
    change Continuous (fun t : ℝ => t*(t-(q 0 : ℝ)-1)*(t-(q 1 : ℝ)-1)*
      (t-(q 2 : ℝ)-1)*(t-(q 3 : ℝ)-1)-
      (t-1)^2*(2*t-(q 0 : ℝ)-q 2-2)*(2*t-(q 1 : ℝ)-q 3-2))
    fun_prop
  have hf0 : f 0 = -(((q 0 : ℝ)+q 2+2)*((q 1 : ℝ)+q 3+2)) := by
    dsimp [f,pureQPolynomial]; ring
  have hf1 : f 1 = (q 0 : ℝ)*q 1*q 2*q 3 := by dsimp [f,pureQPolynomial]; ring
  have h0 : 0 < ((q 0 : ℝ)+q 2+2)*((q 1 : ℝ)+q 3+2) := by positivity
  have h1 : 0 < (q 0 : ℝ)*q 1*q 2*q 3 :=
    mul_pos (mul_pos (mul_pos (by exact_mod_cast hq 0) (by exact_mod_cast hq 1))
      (by exact_mod_cast hq 2)) (by exact_mod_cast hq 3)
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 0) (f 1) := by rw [hf0,hf1]; constructor <;> linarith
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzero
  exact pure_q_small_root_nonintegral q t ht.1 ht.2 hft
#print axioms Paper7B4Analytic.pure_q_four_positive_nonintegral

theorem pure_q_three_positive_nonintegral (q : Fin 4 → ℕ)
    (hq0 : 0 < q 0) (hq1 : 0 < q 1) (hq2 : 0 < q 2) (hq3 : q 3 = 0) :
    ¬ IsIntegralGraph (SG 4 (fun _ => 0) q) := by
  let f : ℝ → ℝ := fun t => -pureQThreePolynomial (q 0) (q 1) (q 2) t
  have hcont : Continuous f := by dsimp [f,pureQThreePolynomial]; fun_prop
  have hf0 : f 0 = -(((q 0 : ℝ)+q 2+2)*((q 1 : ℝ)+2)) := by
    dsimp [f,pureQThreePolynomial]; ring
  have hf1 : f 1 = (q 0 : ℝ)*q 1*q 2 := by dsimp [f,pureQThreePolynomial]; ring
  have h0 : 0 < ((q 0 : ℝ)+q 2+2)*((q 1 : ℝ)+2) := by positivity
  have h1 : 0 < (q 0 : ℝ)*q 1*q 2 :=
    mul_pos (mul_pos (by exact_mod_cast hq0) (by exact_mod_cast hq1)) (by exact_mod_cast hq2)
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 0) (f 1) := by rw [hf0,hf1]; constructor <;> linarith
  obtain ⟨t,ht,hft⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn hzero
  have hpoly : pureQPolynomial (q 0) (q 1) (q 2) (q 3) t = 0 := by
    rw [hq3,Nat.cast_zero,pure_q_three_factor]
    have hh : pureQThreePolynomial (q 0) (q 1) (q 2) t = 0 := by
      change -pureQThreePolynomial (q 0) (q 1) (q 2) t = 0 at hft
      linarith
    rw [hh,mul_zero]
  exact pure_q_small_root_nonintegral q t ht.1 ht.2 hpoly
#print axioms Paper7B4Analytic.pure_q_three_positive_nonintegral

theorem pure_q_three_dihedral_nonintegral (q : Fin 4 → ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (h0 : 0 < (q ∘ σ) 0) (h1 : 0 < (q ∘ σ) 1)
    (h2 : 0 < (q ∘ σ) 2) (h3 : (q ∘ σ) 3 = 0) :
    ¬ IsIntegralGraph (SG 4 (fun _ => 0) q) := by
  intro hG
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 (fun _ => 0) q
    (fun _ => 0) (q ∘ σ) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  exact pure_q_three_positive_nonintegral (q ∘ σ) h0 h1 h2 h3 hI
#print axioms Paper7B4Analytic.pure_q_three_dihedral_nonintegral

theorem pure_q_integral_two_zero_sites (q : Fin 4 → ℕ)
    (hG : IsIntegralGraph (SG 4 (fun _ => 0) q)) :
    ∃ i j : Fin 4, i ≠ j ∧ q i = 0 ∧ q j = 0 := by
  by_cases hfull : ∀ i, 0 < q i
  · exact False.elim (pure_q_four_positive_nonintegral q hfull hG)
  obtain ⟨i,hi⟩ : ∃ i : Fin 4, q i = 0 := by
    push Not at hfull
    obtain ⟨i,hi⟩ := hfull
    exact ⟨i,by omega⟩
  by_cases htwo : ∃ j : Fin 4, j ≠ i ∧ q j = 0
  · obtain ⟨j,hji,hj⟩ := htwo
    exact ⟨i,j,Ne.symm hji,hi,hj⟩
  have hpos : ∀ j : Fin 4, j ≠ i → 0 < q j := by
    intro j hji
    by_contra hh
    exact htwo ⟨j,hji,by omega⟩
  let σ : Fin 4 → Fin 4 := fun k => k+(i+1)
  have hσ : IsDihedral 4 σ := by
    refine ⟨i+1,Or.inl ?_⟩
    intro k
    fin_cases i <;> fin_cases k <;> decide
  have h0 : 0 < (q ∘ σ) 0 := by apply hpos; fin_cases i <;> decide
  have h1 : 0 < (q ∘ σ) 1 := by apply hpos; fin_cases i <;> decide
  have h2 : 0 < (q ∘ σ) 2 := by apply hpos; fin_cases i <;> decide
  have h3 : (q ∘ σ) 3 = 0 := by
    have hindex : σ 3 = i := by fin_cases i <;> rfl
    change q (σ 3) = 0
    rw [hindex]
    exact hi
  exact False.elim (pure_q_three_dihedral_nonintegral q σ hσ h0 h1 h2 h3 hG)
#print axioms Paper7B4Analytic.pure_q_integral_two_zero_sites

end Paper7B4Analytic
