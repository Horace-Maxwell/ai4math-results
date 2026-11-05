import Research.Backfill.Paper7.SunSchurPolynomial
import Research.Backfill.Paper7.ClearedConsequences

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Cleared

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- The exact integer-polynomial identity, with all exponents nonnegative and
without an evaluation-point restriction in its conclusion. -/
theorem cleared_identity (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    X ^ totalP b p * (X ^ 2 - 1) ^ totalQ b q * clearedF b p q =
      X ^ b * (X ^ 2 - 1) ^ b * graphPhi (SG b p q) := by
  classical
  let F : Type := FractionRing (Polynomial ℤ)
  let ι : Polynomial ℤ →+* F := algebraMap (Polynomial ℤ) F
  have hinj : Function.Injective ι := IsFractionRing.injective (Polynomial ℤ) F
  have hx : ι X ≠ 0 := by
    intro h
    have hX : (X : Polynomial ℤ) = 0 := hinj (by simpa only [map_zero] using h)
    exact Polynomial.X_ne_zero hX
  have hquad : (ι X) ^ 2 - 1 ≠ 0 := by
    intro h
    have hB : (X ^ 2 - 1 : Polynomial ℤ) = 0 :=
      hinj (by simpa only [map_sub, map_pow, map_one, map_zero] using h)
    exact (monic_X_pow_sub_one (R := ℤ) (n := 2) (by decide)).ne_zero hB
  have heval : Polynomial.eval₂RingHom (Int.castRingHom F) (ι X) = ι := by
    apply Polynomial.ringHom_ext
    · intro z
      change (Polynomial.C z).eval₂ (Int.castRingHom F) (ι X) = ι (Polynomial.C z)
      rw [Polynomial.eval₂_C]
      have hC : Polynomial.C z = (z : Polynomial ℤ) := map_intCast Polynomial.C z
      rw [hC, map_intCast]
      rfl
    · exact Polynomial.eval₂_X _ _
  apply hinj
  have h := eval_cleared_identity b p q hb (ι X) hx hquad
  rw [heval] at h
  simpa only [map_mul, map_pow, map_sub, map_one] using h

#print axioms Paper7Cleared.cleared_identity

theorem check_ClearedCharacteristicPolynomial :
    BackfillPaper7.Challenge.Legacy.Algebra.ClearedCharacteristicPolynomial := by
  intro b p q hb
  have h := cleared_identity b p q hb
  exact ⟨h, monic_degree_of_cleared_identity b p q h⟩

#print axioms Paper7Cleared.check_ClearedCharacteristicPolynomial

end Paper7Cleared
