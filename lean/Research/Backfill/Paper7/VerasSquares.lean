import Research.Backfill.Paper7.VerasPolynomial
import Research.Backfill.Paper7.SpectrumFactorization

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Veras

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- An actual quadratic factor of an integral graph gives an integer square.
The root used here belongs to the complex spectrum of the original matrix. -/
theorem integer_square_of_quadratic_dvd {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ)
    (hG : IsIntegralGraph G)
    (hdiv : (X ^ 2 - C (n : ℤ) : Polynomial ℤ) ∣ graphPhi G) :
    ∃ z : ℤ, z ^ 2 = (n : ℤ) := by
  let μ : ℂ := (Real.sqrt (n : ℝ) : ℂ)
  have hμ : μ ^ 2 = (n : ℂ) := by
    dsimp [μ]
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
  have hroot : Polynomial.IsRoot
      ((X ^ 2 - C (n : ℤ) : Polynomial ℤ).map (Int.castRingHom ℂ)) μ := by
    simp [Polynomial.IsRoot, hμ]
  have hrootG : Polynomial.IsRoot ((graphPhi G).map (Int.castRingHom ℂ)) μ := by
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, Polynomial.map_mul]
    simp only [Polynomial.IsRoot, Polynomial.eval_mul, hroot.eq_zero, zero_mul]
  rw [Paper7Spectrum.graphPhi_map G ℂ] at hrootG
  obtain ⟨z, hz⟩ := hG μ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hrootG)
  have hz2 : (z : ℂ) ^ 2 = (n : ℂ) := by
    rw [← hz]
    exact hμ
  exact ⟨z, by exact_mod_cast hz2⟩
#print axioms Paper7Veras.integer_square_of_quadratic_dvd

theorem veras_necessary_squares (a : ℕ) (ha : 1 ≤ a)
    (hG : IsIntegralGraph (sunGraph 4 (VerasSquare a))) :
    ∃ u v : ℤ, u ^ 2 = (a : ℤ) ∧ v ^ 2 = 2 * (a : ℤ) + 4 := by
  have hdivA : (X ^ 2 - C (a : ℤ) : Polynomial ℤ) ∣
      graphPhi (sunGraph 4 (VerasSquare a)) := by
    rw [veras_graphPhi a ha]
    refine ⟨X ^ (4 * a - 2) * (X ^ 2 - C (a : ℤ)) *
      (X ^ 2 - C (2 * (a : ℤ) + 4)), ?_⟩
    ring
  have hdivB : (X ^ 2 - C ((2 * a + 4 : ℕ) : ℤ) : Polynomial ℤ) ∣
      graphPhi (sunGraph 4 (VerasSquare a)) := by
    rw [veras_graphPhi a ha]
    norm_num
  obtain ⟨u, hu⟩ := integer_square_of_quadratic_dvd _ a hG hdivA
  obtain ⟨v, hv⟩ := integer_square_of_quadratic_dvd _ (2 * a + 4) hG hdivB
  exact ⟨u, v, hu, by simpa using hv⟩
#print axioms Paper7Veras.veras_necessary_squares

def verasRootList (a : ℕ) (u v : ℤ) : List ℤ :=
  List.replicate (4 * a - 2) 0 ++ [u, u, -u, -u, v, -v]
#print axioms Paper7Veras.verasRootList

theorem veras_root_product (a : ℕ) (u v : ℤ) :
    ((verasRootList a u v).map (fun z => X - C z)).prod =
      X ^ (4 * a - 2) * (X ^ 2 - C (u ^ 2)) ^ 2 * (X ^ 2 - C (v ^ 2)) := by
  simp [verasRootList, map_pow]
  ring
#print axioms Paper7Veras.veras_root_product

theorem veras_integral_of_squares (a : ℕ) (ha : 1 ≤ a) (u v : ℤ)
    (hu : u ^ 2 = (a : ℤ)) (hv : v ^ 2 = 2 * (a : ℤ) + 4) :
    IsIntegralGraph (sunGraph 4 (VerasSquare a)) := by
  classical
  have hf : graphPhi (sunGraph 4 (VerasSquare a)) =
      ((verasRootList a u v).map (fun z => X - C z)).prod := by
    rw [veras_graphPhi a ha, veras_root_product, hu, hv]
  apply (Paper7Spectrum.integral_iff_integerFactorization _).mpr
  exact ⟨(verasRootList a u v).toFinset, verasRootList a u v,
    fun z hz => List.mem_toFinset.mpr hz, hf⟩
#print axioms Paper7Veras.veras_integral_of_squares

/-- The full square criterion, including the necessity used for minimality. -/
theorem veras_integral_iff_squares (a : ℕ) (ha : 1 ≤ a) :
    IsIntegralGraph (sunGraph 4 (VerasSquare a)) ↔
      ∃ u v : ℤ, u ^ 2 = (a : ℤ) ∧ v ^ 2 = 2 * (a : ℤ) + 4 := by
  constructor
  · exact veras_necessary_squares a ha
  · rintro ⟨u, v, hu, hv⟩
    exact veras_integral_of_squares a ha u v hu hv
#print axioms Paper7Veras.veras_integral_iff_squares

theorem veras_parameter_minimum (a : ℕ) (ha : 1 ≤ a) (u v : ℤ)
    (hu : u ^ 2 = (a : ℤ)) (hv : v ^ 2 = 2 * (a : ℤ) + 4) : 16 ≤ a := by
  by_contra h
  have ha' : (a : ℤ) < 16 := by exact_mod_cast (show a < 16 by omega)
  have huLower : -3 ≤ u := by
    by_contra hh
    have hbad : u ≤ -4 := by omega
    nlinarith [sq_nonneg (u + 4)]
  have huUpper : u ≤ 3 := by
    by_contra hh
    have hbad : 4 ≤ u := by omega
    nlinarith [sq_nonneg (u - 4)]
  have hvLower : -5 ≤ v := by
    by_contra hh
    have hbad : v ≤ -6 := by omega
    nlinarith [sq_nonneg (v + 6)]
  have hvUpper : v ≤ 5 := by
    by_contra hh
    have hbad : 6 ≤ v := by omega
    nlinarith [sq_nonneg (v - 6)]
  interval_cases u <;> interval_cases v <;> norm_num at hu hv <;> omega
#print axioms Paper7Veras.veras_parameter_minimum

end Paper7Veras
