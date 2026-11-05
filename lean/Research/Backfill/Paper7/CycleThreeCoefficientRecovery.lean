import Research.Backfill.Paper7.CycleThreeResidualFactorization

/-! Explicit coefficient normal forms and algebraic parameter recovery.
These symbolic identities do not assert any finite exclusion result. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open Polynomial

/-- Natural parameters are cast individually, avoiding truncated subtraction. -/
theorem oneQ_normal_form (p : Fin 3 → ℕ) (q : ℕ) :
    triangleResidualOneQ p q =
      X ^ 8 - C ((p 0 : ℤ) + p 1 + p 2 + q + 4) * X ^ 6 - 2 * X ^ 5 +
      C ((p 1 : ℤ) * p 2 + ((p 0 : ℤ) + q + 2) * ((p 1 : ℤ) + p 2) +
        2 * (p 0 : ℤ) + q + 3) * X ^ 4 + 2 * X ^ 3 -
      C ((1 + (p 0 : ℤ) + q) * p 1 * p 2 + ((p 0 : ℤ) + 1) *
        ((p 1 : ℤ) + p 2) + p 0) * X ^ 2 + C ((p 0 : ℤ) * p 1 * p 2) := by
  simp [triangleResidualOneQ, triangleDiagonal]
  ring
#print axioms Paper7CycleThree.oneQ_normal_form

theorem offZero_normal_form (b c u v : ℕ) :
    triangleResidualOffZero b c u v =
      X ^ 8 - C ((b : ℤ) + c + u + v + 5) * X ^ 6 - 2 * X ^ 5 +
      C ((b : ℤ) + (1 + (b : ℤ) + v) * (1 + (u : ℤ) + c) +
        (1 + (u : ℤ)) * c + (1 + (u : ℤ)) + (1 + (b : ℤ) + v) + c + 4) * X ^ 4 +
      4 * X ^ 3 - C ((b : ℤ) * (1 + (u : ℤ) + c) +
        (1 + (b : ℤ) + v) * (1 + (u : ℤ)) * c + (1 + (u : ℤ)) +
        (1 + (b : ℤ) + v) + b + 2 * (c : ℤ) + 1) * X ^ 2 - 2 * X +
      C ((b : ℤ) * (1 + (u : ℤ)) * c + b + c) := by
  simp [triangleResidualOffZero, triangleDiagonal]
  ring
#print axioms Paper7CycleThree.offZero_normal_form

theorem atZero_normal_form (a b u v : ℕ) :
    triangleResidualAtZero a b u v =
      X ^ 8 - C ((a : ℤ) + b + u + v + 5) * X ^ 6 - 2 * X ^ 5 +
      C ((a : ℤ) + b + (1 + (a : ℤ) + u) * (1 + (b : ℤ) + v) +
        (1 + (a : ℤ) + u) + (1 + (b : ℤ) + v) + 4) * X ^ 4 + 4 * X ^ 3 -
      C ((1 + (a : ℤ) + u) * b + (1 + (b : ℤ) + v) * a +
        (1 + (a : ℤ) + u) + (1 + (b : ℤ) + v) + a + b + 1) * X ^ 2 - 2 * X +
      C ((a : ℤ) * b + a + b) := by
  simp [triangleResidualAtZero, triangleDiagonal]
  ring
#print axioms Paper7CycleThree.atZero_normal_form

theorem oneQ_coefficient_data (p : Fin 3 → ℕ) (q : ℕ) :
    (triangleResidualOneQ p q).coeff 7 = 0 ∧
    (triangleResidualOneQ p q).coeff 6 = -((p 0 : ℤ) + p 1 + p 2 + q + 4) ∧
    (triangleResidualOneQ p q).coeff 5 = -2 ∧
    (triangleResidualOneQ p q).coeff 4 = (p 1 : ℤ) * p 2 +
      ((p 0 : ℤ) + q + 2) * ((p 1 : ℤ) + p 2) + 2 * (p 0 : ℤ) + q + 3 ∧
    (triangleResidualOneQ p q).coeff 3 = 2 ∧
    (triangleResidualOneQ p q).coeff 1 = 0 ∧
    (triangleResidualOneQ p q).coeff 0 = (p 0 : ℤ) * p 1 * p 2 := by
  rw [oneQ_normal_form]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  norm_num
#print axioms Paper7CycleThree.oneQ_coefficient_data

theorem offZero_coefficient_data (b c u v : ℕ) :
    (triangleResidualOffZero b c u v).coeff 7 = 0 ∧
    (triangleResidualOffZero b c u v).coeff 6 = -((b : ℤ) + c + u + v + 5) ∧
    (triangleResidualOffZero b c u v).coeff 5 = -2 ∧
    (triangleResidualOffZero b c u v).coeff 3 = 4 ∧
    (triangleResidualOffZero b c u v).coeff 1 = -2 ∧
    (triangleResidualOffZero b c u v).coeff 0 = (b : ℤ) * (1 + (u : ℤ)) * c + b + c := by
  rw [offZero_normal_form]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num
#print axioms Paper7CycleThree.offZero_coefficient_data

theorem atZero_coefficient_data (a b u v : ℕ) :
    (triangleResidualAtZero a b u v).coeff 7 = 0 ∧
    (triangleResidualAtZero a b u v).coeff 6 = -((a : ℤ) + b + u + v + 5) ∧
    (triangleResidualAtZero a b u v).coeff 5 = -2 ∧
    (triangleResidualAtZero a b u v).coeff 4 = (a : ℤ) + b +
      (1 + (a : ℤ) + u) * (1 + (b : ℤ) + v) + (1 + (a : ℤ) + u) +
      (1 + (b : ℤ) + v) + 4 ∧
    (triangleResidualAtZero a b u v).coeff 3 = 4 ∧
    (triangleResidualAtZero a b u v).coeff 1 = -2 ∧
    (triangleResidualAtZero a b u v).coeff 0 = (a : ℤ) * b + a + b := by
  rw [atZero_normal_form]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
  norm_num
#print axioms Paper7CycleThree.atZero_coefficient_data

/-- For fixed root coefficients and s=b+c, both a and b*c are the two roots
of one quadratic. The second quadratic recovers b and c. This includes zeros. -/
theorem oneQ_recovery_discriminants (a b c q : ℤ) :
    let T := a + b + c + q
    let B := b*c + (a+q+2)*(b+c) + 2*a + q + 3
    let s := b+c
    let K := B + s^2 - (T+1)*s - T - 3
    K = a+b*c ∧ (a-b*c)^2 = K^2-4*(a*b*c) ∧ (b-c)^2 = s^2-4*(b*c) := by
  dsimp
  constructor
  · ring
  · constructor <;> ring
#print axioms Paper7CycleThree.oneQ_recovery_discriminants

/-- For each bounded u,b the constant coefficient recovers c by an exact
positive-denominator linear equation. No division or zero case is discarded. -/
theorem offZero_constant_recovery (b c u : ℤ) :
    (b*(1+u)*c+b+c)-b = (b*(1+u)+1)*c := by
  ring
#print axioms Paper7CycleThree.offZero_constant_recovery

/-- The constant coefficient recovers a,b by positive factor pairs. Then the
sum/product of A=1+a+u and B=1+b+v recovers the q parameters quadratically. -/
theorem atZero_recovery_identities (a b u v : ℤ) :
    let A := 1+a+u
    let B := 1+b+v
    (a*b+a+b)+1 = (a+1)*(b+1) ∧
      (A-B)^2 = (A+B)^2-4*(a+b+A*B+A+B+4-a-b-(A+B)-4) := by
  dsimp
  constructor <;> ring
#print axioms Paper7CycleThree.atZero_recovery_identities

end Paper7CycleThree
