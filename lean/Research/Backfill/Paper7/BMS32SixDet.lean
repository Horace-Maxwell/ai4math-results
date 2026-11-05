import Mathlib

/-! Exact six-cycle determinant algebra for the frozen C61 polynomial.
This source is an uncompiled candidate. -/

set_option autoImplicit false
set_option maxRecDepth 4096

open scoped Matrix

namespace Paper7BMS32

/-- The six diagonal entries are in their actual cyclic order.  This is a
polynomial identity over every commutative ring. -/
theorem det_six_reflection {R : Type*} [CommRing R] (a b c d : R) :
    (!![a,d,0,0,0,d;
        d,b,d,0,0,0;
        0,d,b,d,0,0;
        0,0,d,c,d,0;
        0,0,0,d,b,d;
        d,0,0,0,d,b] : Matrix (Fin 6) (Fin 6) R).det =
      (b ^ 2 - d ^ 2) *
        (a * c * (b ^ 2 - d ^ 2) - 2 * b * d ^ 2 * (a + c) + 4 * d ^ 4) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.submatrix_apply, Fin.succAbove]
  ring

#print axioms Paper7BMS32.det_six_reflection

/-- The two determinant factors specialize to the claimed integer roots. -/
theorem c61_small_factorization {R : Type*} [CommRing R] (x : R) :
    (((x ^ 2 - 6) ^ 2 - (-x) ^ 2) *
      (x ^ 2 * (x ^ 2 - 12) * ((x ^ 2 - 6) ^ 2 - (-x) ^ 2) -
        2 * (x ^ 2 - 6) * (-x) ^ 2 * (x ^ 2 + (x ^ 2 - 12)) +
        4 * (-x) ^ 4)) =
      x ^ 2 * (x ^ 2 - 4) ^ 2 * (x ^ 2 - 9) ^ 2 * (x ^ 2 - 16) := by
  ring

#print axioms Paper7BMS32.c61_small_factorization

/-- Keep the clearing factors factored during cancellation. -/
theorem c61_reassociation {R : Type*} [CommRing R] (x y u v w : R) :
    x ^ 36 * (y ^ 6 * (x ^ 2 * u ^ 2 * v ^ 2 * w)) =
      (x ^ 6 * y ^ 6) * (x ^ 32 * u ^ 2 * v ^ 2 * w) := by
  ring

#print axioms Paper7BMS32.c61_reassociation

end Paper7BMS32
