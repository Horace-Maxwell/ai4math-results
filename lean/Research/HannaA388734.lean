import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# OEIS A388734: all terms are odd

A388734 (Paul D. Hanna, Sep 20 2025), offset 0, NAME:
"G.f. satisfies A(x) = 1 + x*A(x)^2 + x^2*(1-x)*A(x)^3."
COMMENT: "All terms appear to be odd."

We prove: every integer power series `A` with `A = 1 + x A^2 + x^2 (1-x) A^3` has all
coefficients odd.  (The equation determines `A` uniquely; no normalization is needed.)

Proof: modulo 2, `U = 1/(1-x) = Σ x^n` satisfies the equation:
`(1 + xU^2 + x^2(1-x)U^3)(1-x)^3 = (1-x)^3 + x(1-x) + x^2(1-x) = (1-x)(1 - x + 2x^2)`,
which is `(1-x)^2 = U (1-x)^3` modulo 2.  The equation is a contraction for the `x`-adic
topology (`F - U = x·(F - U)·(...)`), so `F = U`.
-/

noncomputable section
namespace HannaA388734
open PowerSeries

local notation "K" => ZMod 2

lemma two_eq_zero : (2 : PowerSeries K) = 0 := by
  simpa only [map_ofNat, map_zero] using
    congrArg (C : K →+* PowerSeries K) (show (2 : K) = 0 by decide)

/-- `U = Σ_{n ≥ 0} x^n = 1/(1-x)`. -/
def U : PowerSeries K := PowerSeries.mk fun _ => 1

lemma U_mul : U * (1 - X) = 1 := by
  ext n
  rcases n with _ | n <;> simp [U, mul_sub, coeff_succ_mul_X, coeff_one]

lemma U_eq : U = 1 + X * U ^ 2 + X ^ 2 * (1 - X) * U ^ 3 := by
  have hne : ((1 - X) ^ 3 : PowerSeries K) ≠ 0 := by
    apply pow_ne_zero
    intro h
    have := congrArg constantCoeff h
    simp at this
  have h := U_mul
  have key : (U - (1 + X * U ^ 2 + X ^ 2 * (1 - X) * U ^ 3)) * (1 - X) ^ 3 = 0 := by
    linear_combination ((1 - X) ^ 2 - X * (1 - X) * (U * (1 - X) + 1) -
      X ^ 2 * (1 - X) * ((U * (1 - X)) ^ 2 + U * (1 - X) + 1)) * h + (X ^ 3 - X ^ 2) * two_eq_zero
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hne)

/-- The statement in `(ZMod 2)[[X]]`: the reduced equation has the unique solution `U`. -/
theorem residue (F : PowerSeries K) (hF : F = 1 + X * F ^ 2 + X ^ 2 * (1 - X) * F ^ 3) :
    F = U := by
  have hU := U_eq
  have key : ∀ n, X ^ n ∣ F - U := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hid : F - U = X * ((F - U) * ((F + U) + X * (1 - X) * (F ^ 2 + F * U + U ^ 2))) := by
        linear_combination hF - hU
      rw [hid, pow_succ']
      exact mul_dvd_mul_left X (dvd_mul_of_dvd_left ih _)
  have hz : F - U = 0 := by
    ext m
    have h := key (m + 1)
    rw [X_pow_dvd_iff] at h
    simpa using h m (by omega)
  exact sub_eq_zero.mp hz

/-- **A388734: all terms are odd.**  Every integer power series `A` with
`A = 1 + x A^2 + x^2 (1-x) A^3` has only odd coefficients. -/
theorem hanna_a388734 (A : PowerSeries ℤ)
    (hA : A = 1 + X * A ^ 2 + X ^ 2 * (1 - X) * A ^ 3) (n : ℕ) : Odd (coeff n A) := by
  let f : ℤ →+* K := Int.castRingHom K
  have hm : A.map f = 1 + X * (A.map f) ^ 2 + X ^ 2 * (1 - X) * (A.map f) ^ 3 := by
    have h := congrArg (PowerSeries.map f) hA
    simpa only [map_add, map_mul, map_pow, map_sub, map_one, map_X] using h
  have hF := residue (A.map f) hm
  have hcoef := congrArg (coeff n) hF
  rw [coeff_map] at hcoef
  have hU : coeff n U = 1 := by simp [U]
  rw [hU] at hcoef
  rw [← ZMod.intCast_eq_one_iff_odd]
  exact hcoef

end HannaA388734

#print axioms HannaA388734.hanna_a388734
