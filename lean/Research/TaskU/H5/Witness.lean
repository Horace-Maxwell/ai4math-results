import Research.TaskU.H5.WitnessEval
import Mathlib.Tactic.Linarith

namespace TaskU.H5.Proof

open WitnessCertificate

theorem witnessValue : Challenge.witnessValue := by
  have h := Matrix.det_mul left regular
  rw [transformed_eq, Matrix.det_of_isUpperTriangular transformed_upper,
    Matrix.det_of_isLowerTriangular left left_lower, left_diagonal,
    transformed_diagonal, regular_det] at h
  change groupDet witness = 11 * 5 ^ 28
  linarith

#print axioms witnessValue

end TaskU.H5.Proof
