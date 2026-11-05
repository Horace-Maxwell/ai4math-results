import Mathlib

set_option autoImplicit false

noncomputable section

namespace Paper7Cleared

/-- Scaling the Schur complement clears a scalar denominator in the determinant
identity. Both index types may be empty; the invertibility hypothesis is explicit. -/
theorem scaled_schur_det {R : Type*} [CommRing R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R)
    (D : Matrix n n R) [Invertible D] (h : R) :
    D.det * (h • (A - B * ⅟D * C)).det =
      h ^ Fintype.card m * (Matrix.fromBlocks A B C D).det := by
  rw [Matrix.det_smul, Matrix.det_fromBlocks₂₂]
  ring

#print axioms Paper7Cleared.scaled_schur_det

end Paper7Cleared
