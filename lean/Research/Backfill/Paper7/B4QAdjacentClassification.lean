import Research.Backfill.Paper7.B4QAdjacentRoots
import Research.Backfill.Paper7.ControlB4Representatives

/-! SOURCE ONLY. Complete classification of the standard adjacent-q branch
inside the unchanged order bound. The only square-root pairs are derived from
the original spectrum; arithmetic exclusions do not use a candidate table. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

theorem int_square_ne_105 (z : ℤ) : z ^ 2 ≠ 105 := by
  intro he
  by_cases hneg : z ≤ -11
  · nlinarith [sq_nonneg (z + 11)]
  by_cases hpos : 11 ≤ z
  · nlinarith [sq_nonneg (z - 11)]
  have hlo : 0 ≤ z + 10 := by omega
  have hhi : 0 ≤ 10 - z := by omega
  nlinarith [mul_nonneg hlo hhi]
#print axioms Paper7B4Analytic.int_square_ne_105

theorem qadjacent_parameters_of_roots (a b R S : ℕ)
    (hR : 3 ≤ R) (hS : 2 ≤ S) (hSR : S < R)
    (hbound : a + b ≤ 22)
    (hsum : a + b + 5 = R ^ 2 + S ^ 2)
    (hprod : (a + 2) * (b + 2) = R ^ 2 * S ^ 2) :
    (a = 4 ∧ b = 4) ∨ (a = 10 ∧ b = 10) := by
  have hSsq : 4 ≤ S ^ 2 := by simpa using Nat.pow_le_pow_left hS 2
  have hR4 : R ≤ 4 := by
    by_contra hh
    have h5 : 5 ≤ R := by omega
    have hsq := Nat.pow_le_pow_left h5 2
    nlinarith
  have hRcases : R = 3 ∨ R = 4 := by omega
  rcases hRcases with hR3 | hR4
  · have hS2 : S = 2 := by omega
    rw [hR3, hS2] at hsum hprod
    norm_num at hsum hprod
    have hsumZ : (a : ℤ) + b = 8 := by exact_mod_cast (show a + b = 8 by omega)
    have hprodZ : ((a : ℤ) + 2) * ((b : ℤ) + 2) = 36 := by exact_mod_cast hprod
    have hsumSq := congrArg (fun x : ℤ => x ^ 2) hsumZ
    have hsq : ((a : ℤ) - b) ^ 2 = 0 := by nlinarith only [hsumZ, hprodZ, hsumSq]
    have hab := sq_eq_zero_iff.mp hsq
    left
    constructor <;> omega
  · have hScases : S = 2 ∨ S = 3 := by omega
    rcases hScases with hS2 | hS3
    · rw [hR4, hS2] at hsum hprod
      norm_num at hsum hprod
      have hsumZ : (a : ℤ) + b = 15 := by exact_mod_cast (show a + b = 15 by omega)
      have hprodZ : ((a : ℤ) + 2) * ((b : ℤ) + 2) = 64 := by exact_mod_cast hprod
      have hsumSq := congrArg (fun x : ℤ => x ^ 2) hsumZ
      have hsq : ((a : ℤ) - b) ^ 2 = 105 := by nlinarith only [hsumZ, hprodZ, hsumSq]
      exact False.elim (int_square_ne_105 ((a : ℤ) - b) hsq)
    · rw [hR4, hS3] at hsum hprod
      norm_num at hsum hprod
      have hsumZ : (a : ℤ) + b = 20 := by exact_mod_cast (show a + b = 20 by omega)
      have hprodZ : ((a : ℤ) + 2) * ((b : ℤ) + 2) = 144 := by exact_mod_cast hprod
      have hsumSq := congrArg (fun x : ℤ => x ^ 2) hsumZ
      have hsq : ((a : ℤ) - b) ^ 2 = 0 := by nlinarith only [hsumZ, hprodZ, hsumSq]
      have hab := sq_eq_zero_iff.mp hsq
      right
      constructor <;> omega
#print axioms Paper7B4Analytic.qadjacent_parameters_of_roots

theorem qadjacent_integral_parameters (q : Fin 4 → ℕ)
    (hq : 0 < ∑ k, ((0 : ℕ) + q k))
    (hn : nOf 4 (fun _ => 0) q ≤ 49)
    (hG : IsIntegralGraph (SG 4 (fun _ => 0) q))
    (hq2 : q 2 = 0) (hq3 : q 3 = 0) :
    (q 0 = 4 ∧ q 1 = 4) ∨ (q 0 = 10 ∧ q 1 = 10) := by
  obtain ⟨R, S, hR, hS, hSR, hsum, hprod⟩ :=
    qadjacent_two_integer_roots q hq hG hq2 hq3
  have hbound : q 0 + q 1 ≤ 22 := by
    simp only [nOf, Fin.sum_univ_four, hq2, hq3, Nat.add_zero] at hn
    omega
  exact qadjacent_parameters_of_roots (q 0) (q 1) R S hR hS hSR hbound hsum hprod
#print axioms Paper7B4Analytic.qadjacent_integral_parameters

theorem qadjacent_parameters_named (q : Fin 4 → ℕ)
    (hq2 : q 2 = 0) (hq3 : q 3 = 0)
    (hc : (q 0 = 4 ∧ q 1 = 4) ∨ (q 0 = 10 ∧ q 1 = 10)) :
    Nonempty (SG 4 (fun _ => 0) q ≃g sunGraph 4 G20b) ∨
      Nonempty (SG 4 (fun _ => 0) q ≃g sunGraph 4 C42Ten) := by
  rcases hc with ⟨hq0, hq1⟩ | ⟨hq0, hq1⟩
  · have hp : (fun _ : Fin 4 => (0 : ℕ)) = Paper7ThreeRepresentatives.g20bP := by
      funext k
      fin_cases k <;> rfl
    have he : q = Paper7ThreeRepresentatives.g20bQ := by
      funext k
      fin_cases k <;> simp [Paper7ThreeRepresentatives.g20bQ, hq0, hq1, hq2, hq3]
    left
    rw [hp, he, ← Paper7ThreeRepresentatives.g20b_parameters]
    exact ⟨.refl⟩
  · have hp : (fun _ : Fin 4 => (0 : ℕ)) = Paper7Control44.controlP := by
      funext k
      fin_cases k <;> rfl
    have he : q = Paper7Control44.controlQ := by
      funext k
      fin_cases k <;> simp [Paper7Control44.controlQ, hq0, hq1, hq2, hq3]
    right
    rw [hp, he, ← Paper7Control44.control_parameters]
    exact ⟨.refl⟩
#print axioms Paper7B4Analytic.qadjacent_parameters_named

theorem qadjacent_integral_named (q : Fin 4 → ℕ)
    (hq : 0 < ∑ k, ((0 : ℕ) + q k))
    (hn : nOf 4 (fun _ => 0) q ≤ 49)
    (hG : IsIntegralGraph (SG 4 (fun _ => 0) q))
    (hq2 : q 2 = 0) (hq3 : q 3 = 0) :
    Nonempty (SG 4 (fun _ => 0) q ≃g sunGraph 4 G20b) ∨
      Nonempty (SG 4 (fun _ => 0) q ≃g sunGraph 4 C42Ten) :=
  qadjacent_parameters_named q hq2 hq3 (qadjacent_integral_parameters q hq hn hG hq2 hq3)
#print axioms Paper7B4Analytic.qadjacent_integral_named

theorem qadjacent_integral_iff_parameters (q : Fin 4 → ℕ)
    (hq : 0 < ∑ k, ((0 : ℕ) + q k))
    (hn : nOf 4 (fun _ => 0) q ≤ 49) (hq2 : q 2 = 0) (hq3 : q 3 = 0) :
    IsIntegralGraph (SG 4 (fun _ => 0) q) ↔
      (q 0 = 4 ∧ q 1 = 4) ∨ (q 0 = 10 ∧ q 1 = 10) := by
  constructor
  · intro hG
    exact qadjacent_integral_parameters q hq hn hG hq2 hq3
  · intro hc
    rcases qadjacent_parameters_named q hq2 hq3 hc with hg | hc
    · obtain ⟨e⟩ := hg
      exact Paper7Normalize.graphIso_integral _ _ e.symm Paper7ControlB4.g20b_integral
    · obtain ⟨e⟩ := hc
      exact Paper7Normalize.graphIso_integral _ _ e.symm Paper7Control44.control_integral
#print axioms Paper7B4Analytic.qadjacent_integral_iff_parameters

end Paper7B4Analytic
