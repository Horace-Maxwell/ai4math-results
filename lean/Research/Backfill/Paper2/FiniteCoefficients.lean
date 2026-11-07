import Research.Backfill.Paper2.XadicAlgebra

/-! Finite coefficient identities used for the exact data gates and recursions. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.FiniteCoefficients
open PowerSeries
variable {R : Type*} [CommRing R]

theorem coeff_mul_range (F G : PowerSeries R) (n : ℕ) :
    coeff n (F * G) = ∑ j ∈ Finset.range (n + 1), coeff j F * coeff (n - j) G := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem coeff_subst_range (F G : PowerSeries R) (hG : constantCoeff G = 0) (n : ℕ) :
    coeff n (F.subst G) = ∑ j ∈ Finset.range (n + 1), coeff j F * coeff n (G ^ j) := by
  have hs := HasSubst.of_constantCoeff_zero' hG
  rw [coeff_subst' hs]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hj ⊢
  by_contra hnj
  have hd : X ^ j ∣ G ^ j := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hG) j
  rw [X_pow_dvd_iff] at hd
  exact hj (by rw [hd n (by omega), smul_zero])

theorem coeff_one_add_X_pow (n j : ℕ) :
    coeff j ((1 + X : PowerSeries R) ^ n) = (Nat.choose n j : R) := by
  have he : ((1 + X : PowerSeries R) ^ n) =
      ((((1 : Polynomial R) + Polynomial.X) ^ n : Polynomial R) : PowerSeries R) := by simp
  rw [he, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem coeff_h389472_pow (n j : ℕ) :
    coeff j (((X : PowerSeries R) ^ 2 + X ^ 3) ^ n) =
      if 2 * n ≤ j then (Nat.choose n (j - 2 * n) : R) else 0 := by
  have he : (((X : PowerSeries R) ^ 2 + X ^ 3) ^ n) = X ^ (2 * n) * (1 + X) ^ n := by
    rw [show (X : PowerSeries R) ^ 2 + X ^ 3 = X ^ 2 * (1 + X) by ring, mul_pow, ← pow_mul]
  rw [he, coeff_X_pow_mul']
  split_ifs <;> simp only [coeff_one_add_X_pow]

end BackfillPaper2.FiniteCoefficients
#print axioms BackfillPaper2.FiniteCoefficients.coeff_mul_range
#print axioms BackfillPaper2.FiniteCoefficients.coeff_subst_range
#print axioms BackfillPaper2.FiniteCoefficients.coeff_one_add_X_pow
#print axioms BackfillPaper2.FiniteCoefficients.coeff_h389472_pow
