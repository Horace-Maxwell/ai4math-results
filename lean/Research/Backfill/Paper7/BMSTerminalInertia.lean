import Research.Backfill.Paper7.BMSCoreComparison
import Research.Backfill.Paper7.InertiaBlockElimination

/-! Exact terminal P3 certificates. Source-only candidate: no execution receipt. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace Paper7BMS
open BackfillPaper7.Challenge Paper7Inertia Paper7Comparison

def terminalBlock : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 0, 1; 0, 1, 0]
#print axioms Paper7BMS.terminalBlock

def terminalShift (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  terminalBlock - Matrix.diagonal (fun _ => x)
#print axioms Paper7BMS.terminalShift

theorem terminalBlock_isHermitian : terminalBlock.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [terminalBlock]
#print axioms Paper7BMS.terminalBlock_isHermitian

theorem terminalShift_isHermitian (x : ℝ) : (terminalShift x).IsHermitian :=
  terminalBlock_isHermitian.sub (Matrix.isHermitian_diagonal _)
#print axioms Paper7BMS.terminalShift_isHermitian

def terminalInverse (x : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (x * (2-x^2))⁻¹ • !![x^2-1, x, 1; x, x^2, x; 1, x, x^2-1]
#print axioms Paper7BMS.terminalInverse

theorem terminal_inverse_right (x : ℝ) (hx : x*(2-x^2) ≠ 0) :
    terminalShift x * terminalInverse x = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [terminalShift, terminalBlock, terminalInverse, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail] <;>
    field_simp [hx, (mul_ne_zero_iff.mp hx).1, (mul_ne_zero_iff.mp hx).2] <;> ring
#print axioms Paper7BMS.terminal_inverse_right

theorem terminal_inverse_eq (x : ℝ) (hx : x*(2-x^2) ≠ 0) :
    (terminalShift x)⁻¹ = terminalInverse x :=
  Matrix.inv_eq_right_inv (terminal_inverse_right x hx)
#print axioms Paper7BMS.terminal_inverse_eq

def terminalBasisAtOne : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 1; 0, 0, 1; 0, 1, 1]
#print axioms Paper7BMS.terminalBasisAtOne

def terminalBasisAtOneInv : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -1, 0; 0, -1, 1; 0, 1, 0]
#print axioms Paper7BMS.terminalBasisAtOneInv

theorem terminalBasisAtOne_inverse :
    terminalBasisAtOne * terminalBasisAtOneInv = 1 ∧
      terminalBasisAtOneInv * terminalBasisAtOne = 1 := by
  constructor <;> apply Matrix.ext <;> intro i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [terminalBasisAtOne, terminalBasisAtOneInv, Matrix.mul_apply,
      Fin.sum_univ_succ]
#print axioms Paper7BMS.terminalBasisAtOne_inverse

theorem terminalBasisAtOne_diagonal :
    terminalBasisAtOneᵀ * terminalShift 1 * terminalBasisAtOne =
      Matrix.diagonal ![-1, -1, (1 : ℝ)] := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [terminalBasisAtOne, terminalShift, terminalBlock, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]
#print axioms Paper7BMS.terminalBasisAtOne_diagonal

theorem terminal_nPos_one : nPos (terminalShift 1) = 1 := by
  have hi := (inertia_congruence (terminalShift 1) terminalBasisAtOne
    terminalBasisAtOneInv (terminalShift_isHermitian 1)
    terminalBasisAtOne_inverse.1 terminalBasisAtOne_inverse.2).1
  rw [terminalBasisAtOne_diagonal] at hi
  rw [← hi, (inertia_diagonal ![-1, -1, (1 : ℝ)]).1]
  have hs : {i : Fin 3 | 0 < (![-1, -1, (1 : ℝ)] : Fin 3 → ℝ) i} = {2} := by
    ext i
    fin_cases i <;> norm_num
  rw [hs]
  simp
#print axioms Paper7BMS.terminal_nPos_one

theorem terminal_rho_quadratic (z : Fin 3 → ℝ) :
    (terminalShift rho).toQuadraticForm' z =
      -rho * (z 0-z 1/rho)^2 - rho * (z 2-z 1/rho)^2 +
        (2/rho-rho) * (z 1)^2 := by
  have hr : rho ≠ 0 := ne_of_gt (lt_trans zero_lt_one one_lt_rho)
  simp only [quadratic_apply, Matrix.mulVec, dotProduct]
  norm_num [terminalShift, terminalBlock, Matrix.diagonal, Fin.sum_univ_succ]
  field_simp [hr]
  ring
#print axioms Paper7BMS.terminal_rho_quadratic

theorem terminal_rho_quadratic_nonpos (z : Fin 3 → ℝ) :
    (terminalShift rho).toQuadraticForm' z ≤ 0 := by
  have hr : 0 < rho := lt_trans zero_lt_one one_lt_rho
  have hc : 2/rho-rho < 0 := by
    have h' : 2/rho < rho := (div_lt_iff₀ hr).2 (by
      simpa only [pow_two] using two_lt_rho_sq)
    linarith
  rw [terminal_rho_quadratic]
  have h₀ := mul_nonneg hr.le (sq_nonneg (z 0-z 1/rho))
  have h₂ := mul_nonneg hr.le (sq_nonneg (z 2-z 1/rho))
  have h₁ := mul_nonpos_of_nonpos_of_nonneg hc.le (sq_nonneg (z 1))
  linarith
#print axioms Paper7BMS.terminal_rho_quadratic_nonpos

theorem terminal_nPos_rho : nPos (terminalShift rho) = 0 := by
  have hzero : nPos (Matrix.diagonal (fun _ : Fin 3 => (0 : ℝ))) = 0 := by
    rw [(inertia_diagonal (fun _ : Fin 3 => (0 : ℝ))).1]
    simp
  have hle := (inertia_mono (terminalShift rho)
    (Matrix.diagonal (fun _ : Fin 3 => (0 : ℝ))) (terminalShift_isHermitian rho)
    (Matrix.isHermitian_diagonal _) (fun z => by
      simpa only [quadratic_diagonal, QuadraticMap.weightedSumSquares_apply,
        zero_smul, Finset.sum_const_zero] using terminal_rho_quadratic_nonpos z)).1
  omega
#print axioms Paper7BMS.terminal_nPos_rho

end Paper7BMS
