import Research.Backfill.Paper7.BMSSharpEndpoint
import Research.Backfill.Paper7.InertiaComparison

/-! Direct comparison at the sharp endpoint; zero directions are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Paper7BMS
open BackfillPaper7.Challenge Paper7Inertia Paper7Comparison

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def terminalCoreShift (M : Matrix ι ι ℝ) (v : ι) (x : ℝ) : Matrix ι ι ℝ :=
  M - Matrix.diagonal (fun i => x + terminalResolvent x * (if i = v then 1 else 0))
#print axioms Paper7BMS.terminalCoreShift

omit [Fintype ι] in
theorem terminalCoreShift_isHermitian (M : Matrix ι ι ℝ) (v : ι) (x : ℝ)
    (hM : M.IsHermitian) : (terminalCoreShift M v x).IsHermitian :=
  hM.sub (Matrix.isHermitian_diagonal _)
#print axioms Paper7BMS.terminalCoreShift_isHermitian

omit [Fintype ι] in
theorem terminalCoreShift_one (M : Matrix ι ι ℝ) (v : ι) :
    terminalCoreShift M v 1 = M - Matrix.diagonal (fun _ => 1) := by
  simp only [terminalCoreShift, terminalResolvent_one, zero_mul, add_zero]
#print axioms Paper7BMS.terminalCoreShift_one

omit [Fintype ι] in
theorem rho_core_diagonal_ge_one (v i : ι) :
    1 ≤ rho + terminalResolvent rho * (if i = v then 1 else 0) := by
  rw [terminalResolvent_rho]
  by_cases h : i = v
  · simp only [h, ite_true, mul_one]
    linarith
  · simp only [h, ite_false, mul_zero, add_zero]
    exact one_lt_rho.le
#print axioms Paper7BMS.rho_core_diagonal_ge_one

theorem quadratic_sub_apply (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    (A - B).toQuadraticForm' x = A.toQuadraticForm' x - B.toQuadraticForm' x := by
  simp only [quadratic_apply, Matrix.sub_mulVec, dotProduct_sub]
#print axioms Paper7BMS.quadratic_sub_apply

theorem terminalCoreShift_quadratic_le (M : Matrix ι ι ℝ) (v : ι) (x : ι → ℝ) :
    (terminalCoreShift M v rho).toQuadraticForm' x ≤
      (terminalCoreShift M v 1).toQuadraticForm' x := by
  rw [terminalCoreShift_one]
  change (M - Matrix.diagonal _).toQuadraticForm' x ≤ _
  rw [quadratic_sub_apply, quadratic_sub_apply]
  apply sub_le_sub_left
  rw [quadratic_diagonal, quadratic_diagonal]
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, one_mul]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_right (rho_core_diagonal_ge_one v i)
    (mul_self_nonneg (x i))
  simpa only [one_mul] using h
#print axioms Paper7BMS.terminalCoreShift_quadratic_le

theorem terminalCoreShift_nPos_le (M : Matrix ι ι ℝ) (v : ι) (hM : M.IsHermitian) :
    nPos (terminalCoreShift M v rho) ≤ nPos (terminalCoreShift M v 1) :=
  (inertia_mono _ _ (terminalCoreShift_isHermitian M v rho hM)
    (terminalCoreShift_isHermitian M v 1 hM) (terminalCoreShift_quadratic_le M v)).1
#print axioms Paper7BMS.terminalCoreShift_nPos_le

end Paper7BMS
