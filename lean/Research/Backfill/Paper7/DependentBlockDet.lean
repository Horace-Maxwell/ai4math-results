import Mathlib

set_option autoImplicit false

noncomputable section

namespace Paper7Cleared

/-- The determinant of a dependent block diagonal matrix is the product of the
block determinants. The outer index and individual fibers may be empty. -/
theorem det_blockDiagonal' {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (D : ∀ i, Matrix (n i) (n i) R) :
    (Matrix.blockDiagonal' D).det = ∏ i, (D i).det := by
  classical
  rw [(Matrix.blockTriangular_blockDiagonal' D).det_fintype]
  apply Finset.prod_congr rfl
  intro i _hi
  have hblock :
      ((Matrix.blockDiagonal' D).toSquareBlock Sigma.fst i).submatrix
          (Equiv.sigmaSubtype (β := n) i).symm
          (Equiv.sigmaSubtype (β := n) i).symm = D i := by
    ext a b
    change Matrix.blockDiagonal' D ⟨i, a⟩ ⟨i, b⟩ = D i a b
    exact Matrix.blockDiagonal'_apply_eq D i a b
  calc
    ((Matrix.blockDiagonal' D).toSquareBlock Sigma.fst i).det =
        (((Matrix.blockDiagonal' D).toSquareBlock Sigma.fst i).submatrix
          (Equiv.sigmaSubtype (β := n) i).symm
          (Equiv.sigmaSubtype (β := n) i).symm).det :=
      (Matrix.det_submatrix_equiv_self (Equiv.sigmaSubtype (β := n) i).symm
        ((Matrix.blockDiagonal' D).toSquareBlock Sigma.fst i)).symm
    _ = (D i).det := congrArg Matrix.det hblock

#print axioms Paper7Cleared.det_blockDiagonal'

/-- If every block determinant is a unit, taking the nonsingular matrix inverse
commutes with dependent block diagonal assembly. No nonempty fiber is required. -/
theorem inv_blockDiagonal'_of_isUnit_det {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (D : ∀ i, Matrix (n i) (n i) R)
    (hD : ∀ i, IsUnit (D i).det) :
    (Matrix.blockDiagonal' D)⁻¹ = Matrix.blockDiagonal' (fun i => (D i)⁻¹) := by
  classical
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.blockDiagonal'_mul]
  have hblocks : (fun i => (D i)⁻¹ * D i) =
      (1 : ∀ i, Matrix (n i) (n i) R) := by
    funext i
    exact Matrix.nonsing_inv_mul (D i) (hD i)
  rw [hblocks, Matrix.blockDiagonal'_one]

#print axioms Paper7Cleared.inv_blockDiagonal'_of_isUnit_det

end Paper7Cleared
