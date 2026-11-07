import Research.Backfill.Paper2.Challenge

/-!
The complete polynomial formula for the actual iterate, not just its sampled
coefficients. Over F3, expansion X -> X^3 is linear and equals cubing. Thus
P_m=(E+1)^m(X), and the commuting-operator binomial theorem gives the formula.
-/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.TernaryPolynomial
open Polynomial BackfillPaper2.Challenge
local notation "K" => ZMod 3

theorem check_Rem13_PmMod3 : Rem13_PmMod3 := by
  intro m
  let E : Module.End K K[X] := (Polynomial.expand K 3).toLinearMap
  have it : ∀ n : ℕ, (P184894 n).map (Int.castRingHom K) =
      ((E + 1) ^ n) (X : K[X]) := by
    intro n
    induction n with
    | zero => simp [P184894]
    | succ n ih =>
      calc
        (P184894 (n + 1)).map (Int.castRingHom K) =
            (P184894 n).map (Int.castRingHom K) +
              ((P184894 n).map (Int.castRingHom K)) ^ 3 := by
          rw [P184894, Polynomial.map_add, Polynomial.map_pow]
        _ = ((E + 1) ^ n) X + (((E + 1) ^ n) X) ^ 3 := by rw [ih]
        _ = ((E + 1) * (E + 1) ^ n) X := by
          simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply]
          change ((E + 1) ^ n) X + (((E + 1) ^ n) X) ^ 3 =
            Polynomial.expand K 3 (((E + 1) ^ n) X) + ((E + 1) ^ n) X
          rw [ZMod.expand_card]
          exact add_comm _ _
        _ = ((E + 1) ^ (n + 1)) X := by rw [pow_succ']
  rw [it m]
  rw [LinearMap.congr_fun ((Commute.one_right E).add_pow m) (X : K[X])]
  simp only [LinearMap.sum_apply, one_pow, mul_one,
    Module.End.mul_apply, Module.End.natCast_apply]
  apply Finset.sum_congr rfl
  intro j _
  have he : (E ^ j) (X : K[X]) = X ^ (3 ^ j) := by
    rw [Module.End.pow_apply]
    change (Polynomial.expand K 3)^[j] X = X ^ (3 ^ j)
    rw [← Polynomial.expand_pow, Polynomial.expand_X]
  rw [map_nsmul, he, nsmul_eq_mul, map_natCast]

end BackfillPaper2.TernaryPolynomial
#print axioms BackfillPaper2.TernaryPolynomial.check_Rem13_PmMod3
