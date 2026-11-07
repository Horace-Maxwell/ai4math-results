import Research.Backfill.Paper2.Challenge

/-!
The first three Catalan contracts of the frozen Paper 2 challenge.
The second-derivative calculation follows the published HannaA301933 argument;
no old project theorem or unproved declaration is imported.
-/

set_option autoImplicit false

noncomputable section
namespace BackfillPaper2.CatalanCore

open PowerSeries BackfillPaper2.Challenge

private theorem quadratic_unique {R : Type*} [CommRing R]
    (F G : PowerSeries R) (hF : constantCoeff F = 0) (hG : constantCoeff G = 0)
    (he : F - F ^ 2 = G - G ^ 2) : F = G := by
  have hu : IsUnit (1 - F - G) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hF, hG])
  have hz : (1 - F - G) * (F - G) = 0 := by linear_combination he
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hz)

private theorem two_series_zero : (2 : PowerSeries (ZMod 2)) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  simpa only [map_ofNat, map_zero] using
    congrArg (C : ZMod 2 →+* PowerSeries (ZMod 2)) h

private theorem second_derivative_zero (F : PowerSeries (ZMod 2)) :
    derivative (R := ZMod 2) (derivative (R := ZMod 2) F) = 0 := by
  ext n
  rw [coeff_derivative, coeff_derivative, map_zero]
  have h : (((n + 1) * (n + 1 + 1) : ℕ) : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr (Nat.even_mul_succ_self (n + 1))
  push_cast at h ⊢
  linear_combination (coeff (n + 1 + 1) F) * h

theorem check_CatalanEq : CatalanEq := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, map_X] at h
  change catalanC = X + catalanC ^ 2
  rw [catalanC]
  linear_combination (-(X : PowerSeries ℤ)) * h

theorem check_RC_A301933_catalanIdentity : RC_A301933_catalanIdentity := by
  have hC : catalanC = X + catalanC ^ 2 := check_CatalanEq
  have hD := congrArg (derivative (R := ℤ)) hC
  simp only [map_add, derivative_X, derivative_pow] at hD
  change catalanC * (1 + catalanC * derivative (R := ℤ) catalanC) =
    X * (1 + 2 * catalanC * derivative (R := ℤ) catalanC)
  linear_combination (1 + 2 * catalanC * derivative (R := ℤ) catalanC) * hC -
    catalanC ^ 2 * hD

theorem check_RC_A301933_determines : RC_A301933_determines := by
  intro F hF0 hF
  have e1 : F + F ^ 2 * derivative (R := ZMod 2) F = X := by
    linear_combination hF
  have e2 := congrArg (derivative (R := ZMod 2)) e1
  rw [map_add, Derivation.leibniz, Derivation.leibniz_pow,
    second_derivative_zero, derivative_X] at e2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at e2
  have hDF : derivative (R := ZMod 2) F = 1 := by
    linear_combination e2 -
      (derivative (R := ZMod 2) F *
        (F ^ (2 - 1) * derivative (R := ZMod 2) F)) * two_series_zero
  rw [hDF, mul_one] at e1
  have hFC : F = X + F ^ 2 := by
    linear_combination e1 - F ^ 2 * two_series_zero
  have hC := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2)))
    (show catalanC = X + catalanC ^ 2 from check_CatalanEq)
  simp only [map_add, map_pow, map_X] at hC
  have hC0 : constantCoeff (red 2 catalanC) = 0 := by
    simp [red, catalanC]
  apply quadratic_unique F (red 2 catalanC) hF0 hC0
  change F - F ^ 2 = PowerSeries.map (Int.castRingHom (ZMod 2)) catalanC -
    (PowerSeries.map (Int.castRingHom (ZMod 2)) catalanC) ^ 2
  linear_combination hFC - hC

end BackfillPaper2.CatalanCore

#print axioms BackfillPaper2.CatalanCore.check_CatalanEq
#print axioms BackfillPaper2.CatalanCore.check_RC_A301933_catalanIdentity
#print axioms BackfillPaper2.CatalanCore.check_RC_A301933_determines
