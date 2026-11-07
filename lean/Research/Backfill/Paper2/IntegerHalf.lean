import Research.Backfill.Paper2.FiniteCoefficients

/-! Coefficientwise integer halving, with divisibility proved before each use. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.IntegerHalf
open PowerSeries

def halve (F : PowerSeries ℤ) : PowerSeries ℤ := PowerSeries.mk fun n => coeff n F / 2

theorem halve_zero : halve (0 : PowerSeries ℤ) = 0 := by
  ext n
  simp [halve]

theorem twice_halve (F : PowerSeries ℤ) (heven : ∀ n, (2 : ℤ) ∣ coeff n F) : 2 * halve F = F := by
  ext n
  rw [coeff_ofNat_mul, halve, coeff_mk, mul_comm]
  exact Int.ediv_mul_cancel (heven n)

theorem precision_halve (F G : PowerSeries ℤ) (n : ℕ) (hd : X ^ n ∣ F - G) :
    X ^ n ∣ halve F - halve G := by
  rw [X_pow_dvd_iff] at hd ⊢
  intro m hm
  have he := hd m hm
  rw [map_sub, sub_eq_zero] at he
  simp only [map_sub, halve, coeff_mk, he, sub_self]

theorem precision_cancel_two (F : PowerSeries ℤ) (n : ℕ) (hd : X ^ n ∣ 2 * F) : X ^ n ∣ F := by
  rw [X_pow_dvd_iff] at hd ⊢
  intro m hm
  have he := hd m hm
  rw [coeff_ofNat_mul] at he
  omega

end BackfillPaper2.IntegerHalf
#print axioms BackfillPaper2.IntegerHalf.halve_zero
#print axioms BackfillPaper2.IntegerHalf.twice_halve
#print axioms BackfillPaper2.IntegerHalf.precision_halve
#print axioms BackfillPaper2.IntegerHalf.precision_cancel_two
