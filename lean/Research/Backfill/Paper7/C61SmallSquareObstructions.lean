import Research.Backfill.Paper7.C61ParameterSquares

set_option autoImplicit false
noncomputable section
namespace Paper7C61Small
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Parameters
open scoped BigOperators Classical

/-- An integer maximum and the exact remaining sum give both sides of the
square-moment bound. This retains integrality of the maximum. -/
theorem maximum_moment_interval (p : Fin 6 → ℕ) (P S : ℕ)
    (hP : totalP 6 p = P) (hS : squares 6 p = S) :
    ∃ M : ℤ, 0 ≤ M ∧ M ≤ P ∧ (S : ℤ) ≤ M * P ∧
      M^2 + ((P : ℤ)-M) ≤ S ∧ (S : ℤ) ≤ M^2 + ((P : ℤ)-M)^2 := by
  obtain ⟨M, A, B, hsum, hsq, hAB, hBA, hmax⟩ := maximum_square_data p
  rw [hP] at hsum
  rw [hS] at hsq
  rw [hP, hS] at hmax
  have hsumZ : (P : ℤ) = (M : ℤ) + A := by exact_mod_cast hsum
  have hsqZ : (S : ℤ) = (M : ℤ)^2 + B := by exact_mod_cast hsq
  have hABZ : (A : ℤ) ≤ B := by exact_mod_cast hAB
  have hBAZ : (B : ℤ) ≤ (A : ℤ)^2 := by exact_mod_cast hBA
  have hA : (A : ℤ) = (P : ℤ) - M := by omega
  refine ⟨M, Int.natCast_nonneg M, by omega, ?_, ?_, ?_⟩
  · exact_mod_cast hmax
  · omega
  · rw [hA] at hBAZ
    omega
#print axioms Paper7C61Small.maximum_moment_interval

theorem no_sum8_square48 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 8) (hS : squares 6 p = 48) : False := by
  obtain ⟨M, hM0, _hMP, hmax, hlow, hupp⟩ := maximum_moment_interval p 8 48 hP hS
  norm_num at hmax hlow hupp
  have hM6 : 6 ≤ M := by omega
  have hMlt : M < 7 := by
    by_contra h
    have hM7 : 7 ≤ M := by omega
    have hmul := mul_nonneg (sub_nonneg.mpr hM7) hM0
    nlinarith
  have heq : M = 6 := by omega
  rw [heq] at hupp
  norm_num at hupp
#print axioms Paper7C61Small.no_sum8_square48

theorem no_sum15_square195 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 15) (hS : squares 6 p = 195) : False := by
  obtain ⟨M, hM0, _hMP, hmax, hlow, hupp⟩ := maximum_moment_interval p 15 195 hP hS
  norm_num at hmax hlow hupp
  have hM13 : 13 ≤ M := by omega
  have hMlt : M < 14 := by
    by_contra h
    have hM14 : 14 ≤ M := by omega
    have hmul := mul_nonneg (sub_nonneg.mpr hM14) hM0
    nlinarith
  have heq : M = 13 := by omega
  rw [heq] at hupp
  norm_num at hupp
#print axioms Paper7C61Small.no_sum15_square195

theorem no_sum16_square192 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 16) (hS : squares 6 p = 192) : False := by
  obtain ⟨M, hM0, _hMP, hmax, hlow, hupp⟩ := maximum_moment_interval p 16 192 hP hS
  norm_num at hmax hlow hupp
  have hlo : 12 ≤ M := by omega
  have hhi : M ≤ 13 := by
    by_contra h
    have hM14 : 14 ≤ M := by omega
    have hmul := mul_nonneg (sub_nonneg.mpr hM14) hM0
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Small.no_sum16_square192

theorem no_sum18_square198 (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 18) (hS : squares 6 p = 198) : False := by
  obtain ⟨M, hM0, _hMP, hmax, hlow, hupp⟩ := maximum_moment_interval p 18 198 hP hS
  norm_num at hmax hlow hupp
  have hlo : 11 ≤ M := by omega
  have hhi : M ≤ 13 := by
    by_contra h
    have hM14 : 14 ≤ M := by omega
    have hmul := mul_nonneg (sub_nonneg.mpr hM14) hM0
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  nlinarith
#print axioms Paper7C61Small.no_sum18_square198

theorem sum9_square45_maximum (p : Fin 6 → ℕ)
    (hP : totalP 6 p = 9) (hS : squares 6 p = 45) :
    ∃ k : Fin 6, p k = 6 ∧ (∑ j ∈ Finset.univ.erase k, p j) = 3 ∧
      (∑ j ∈ Finset.univ.erase k, p j^2) = 9 := by
  obtain ⟨k, _hk, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 6))
    p Finset.univ_nonempty
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin 6)) p (Finset.mem_univ k)
  have hsq := Finset.sum_erase_add (Finset.univ : Finset (Fin 6))
    (fun j => p j^2) (Finset.mem_univ k)
  change (∑ j ∈ Finset.univ.erase k, p j) + p k = totalP 6 p at hsum
  change (∑ j ∈ Finset.univ.erase k, p j^2) + p k^2 = squares 6 p at hsq
  rw [hP] at hsum
  rw [hS] at hsq
  have hm : squares 6 p ≤ p k * totalP 6 p := by
    change (∑ j, p j^2) ≤ p k * ∑ j, p j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [pow_two] using Nat.mul_le_mul_right (p j) (hmax j hj)
  rw [hP, hS] at hm
  have hupper := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ.erase k) (fun j _ => Nat.zero_le (p j))
  have hklo : 5 ≤ p k := by omega
  have hkhi : p k ≤ 6 := by
    by_contra h
    have hk7 : 7 ≤ p k := by omega
    have hs7 : 49 ≤ p k ^ 2 := by
      simpa only [pow_two] using Nat.mul_self_le_mul_self hk7
    omega
  have hkne : p k ≠ 5 := by
    intro heq
    have hA : (∑ j ∈ Finset.univ.erase k, p j) = 4 := by omega
    rw [hA] at hupper
    rw [heq] at hsq
    norm_num at hupper hsq
    omega
  have hk6 : p k = 6 := by omega
  refine ⟨k, hk6, ?_, ?_⟩
  · omega
  · rw [hk6] at hsq
    norm_num at hsq
    omega
#print axioms Paper7C61Small.sum9_square45_maximum

end Paper7C61Small
