import Research.Backfill.Paper7.BMS32SixDet
import Research.Backfill.Paper7.ClearedCharacteristicPolynomial

/-! The polynomial of the original frozen 42-vertex Sun graph, through the
accepted exact clearing identity and an explicit six-by-six determinant. -/

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

open scoped Matrix

namespace Paper7BMS32

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- Exact list-valued parameter equality; no replacement graph is introduced. -/
theorem c61_parameters : pq 6 C61P (fun _ => 0) = C61 := by
  funext i
  fin_cases i <;> rfl

#print axioms Paper7BMS32.c61_parameters

theorem c61_totalP : totalP 6 C61P = 36 := by
  norm_num [totalP, C61P, Fin.sum_univ_succ]

#print axioms Paper7BMS32.c61_totalP

theorem c61_totalQ : totalQ 6 (fun _ => 0) = 0 := by
  simp [totalQ]

#print axioms Paper7BMS32.c61_totalQ

theorem cycle_adjacency_six :
    cycleAdjZ 6 =
      (!![0,1,0,0,0,1;
          1,0,1,0,0,0;
          0,1,0,1,0,0;
          0,0,1,0,1,0;
          0,0,0,1,0,1;
          1,0,0,0,1,0] : Matrix (Fin 6) (Fin 6) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cycleAdjZ, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj'] <;>
    decide

#print axioms Paper7BMS32.cycle_adjacency_six

def c61_small_matrix : Matrix (Fin 6) (Fin 6) (Polynomial ℤ) :=
  !![X^2, -X, 0, 0, 0, -X;
     -X, X^2-6, -X, 0, 0, 0;
     0, -X, X^2-6, -X, 0, 0;
     0, 0, -X, X^2-12, -X, 0;
     0, 0, 0, -X, X^2-6, -X;
     -X, 0, 0, 0, -X, X^2-6]

#print axioms Paper7BMS32.c61_small_matrix

/-- Every entry comes from the frozen algebraic definition. -/
theorem c61_cleared_matrix :
    clearedMatrix 6 C61P (fun _ => 0) = (X ^ 2 - 1 : Polynomial ℤ) • c61_small_matrix := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedMatrix, cycle_adjacency_six, C61P, c61_small_matrix,
      Matrix.smul_apply, smul_eq_mul] <;> ring

#print axioms Paper7BMS32.c61_cleared_matrix

theorem c61_small_det :
    c61_small_matrix.det =
      X ^ 2 * (X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16) := by
  rw [c61_small_matrix, det_six_reflection]
  exact c61_small_factorization X

#print axioms Paper7BMS32.c61_small_det

theorem c61_cleared_factorization :
    clearedF 6 C61P (fun _ => 0) =
      (X ^ 2 - 1) ^ 6 *
        (X ^ 2 * (X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16)) := by
  rw [clearedF, c61_cleared_matrix, Matrix.det_smul, Fintype.card_fin, c61_small_det]

#print axioms Paper7BMS32.c61_cleared_factorization

/-- The accepted full polynomial identity allows cancellation in Z[X]. -/
theorem c61_sg_graphPhi :
    graphPhi (SG 6 C61P (fun _ => 0)) =
      X ^ 32 * (X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16) := by
  have hidentity := Paper7Cleared.cleared_identity 6 C61P (fun _ => 0) (by decide)
  rw [c61_totalP, c61_totalQ, c61_cleared_factorization] at hidentity
  simp only [pow_zero, mul_one] at hidentity
  have hn : (X ^ 6 * (X ^ 2 - 1) ^ 6 : Polynomial ℤ) ≠ 0 :=
    (Paper7Cleared.monic_denominator_factor 6 6).ne_zero
  apply mul_left_cancel₀ hn
  calc
    (X ^ 6 * (X ^ 2 - 1) ^ 6) * graphPhi (SG 6 C61P (fun _ => 0)) =
        X ^ 36 * ((X ^ 2 - 1) ^ 6 *
          (X ^ 2 * (X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16))) :=
      hidentity.symm
    _ = (X ^ 6 * (X ^ 2 - 1) ^ 6) *
        (X ^ 32 * (X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16)) :=
      c61_reassociation X (X ^ 2 - 1) (X ^ 2 - 4) (X ^ 2 - 9) (X ^ 2 - 16)

#print axioms Paper7BMS32.c61_sg_graphPhi

theorem c61_graphPhi :
    graphPhi (sunGraph 6 C61) =
      X ^ 32 * (X ^ 2 - 4) ^ 2 * (X ^ 2 - 9) ^ 2 * (X ^ 2 - 16) := by
  exact (congrArg
    (fun L : Fin 6 → List ℕ => graphPhi (sunGraph 6 L))
    c61_parameters).symm.trans c61_sg_graphPhi

#print axioms Paper7BMS32.c61_graphPhi

end Paper7BMS32
