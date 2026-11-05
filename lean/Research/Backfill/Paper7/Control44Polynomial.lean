import Research.Backfill.Paper7.Control44Bridge
import Research.Backfill.Paper7.ClearedCharacteristicPolynomial
import Research.Backfill.Paper7.SetupCardinality

/-! Source-only integer characteristic-polynomial certificate for the actual
44-vertex Sun, with zero single arms and ten two-vertex arms at each of two
adjacent cycle vertices. The historical target name is ControlC42Ten. -/

set_option autoImplicit false
set_option maxRecDepth 4096
open scoped Matrix

namespace Paper7Control44

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

abbrev controlP : Fin 4 → ℕ := ![0,0,0,0]
#print axioms Paper7Control44.controlP

abbrev controlQ : Fin 4 → ℕ := ![10,10,0,0]
#print axioms Paper7Control44.controlQ

/-- Exact equality with the frozen list-valued graph parameter. -/
theorem control_parameters : pq 4 controlP controlQ = C42Ten := by
  funext i
  fin_cases i <;> rfl

#print axioms Paper7Control44.control_parameters

theorem control_order : order 4 C42Ten = 44 := by
  have h := Paper7Setup.sg_order 4 controlP controlQ
  have hn : nOf 4 controlP controlQ = 44 := by
    norm_num [nOf, controlP, controlQ, Fin.sum_univ_succ]
  rw [hn] at h
  simpa only [control_parameters] using h

#print axioms Paper7Control44.control_order

theorem control_pendant_positive : 0 < pendantCount 4 C42Ten := by
  norm_num [pendantCount, C42Ten, Fin.sum_univ_succ]

#print axioms Paper7Control44.control_pendant_positive

theorem cycle_adjacency_four :
    cycleAdjZ 4 = (!![0,1,0,1; 1,0,1,0; 0,1,0,1; 1,0,1,0] :
      Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cycleAdjZ, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj'] <;>
    decide

#print axioms Paper7Control44.cycle_adjacency_four

theorem control_cleared_matrix :
    clearedMatrix 4 controlP controlQ =
      (!![X^2*(X^2-11), -X*(X^2-1), 0, -X*(X^2-1);
          -X*(X^2-1), X^2*(X^2-11), -X*(X^2-1), 0;
          0, -X*(X^2-1), X^2*(X^2-1), -X*(X^2-1);
          -X*(X^2-1), 0, -X*(X^2-1), X^2*(X^2-1)] :
        Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedMatrix, cycle_adjacency_four, controlP, controlQ] <;> ring

#print axioms Paper7Control44.control_cleared_matrix

/-- A degree-sixteen identity over the integers for the actual four-by-four determinant. -/
theorem control_cleared_factorization :
    clearedF 4 controlP controlQ =
      X ^ 6 * (X ^ 2 - 1) ^ 3 * (X ^ 2 - 9) * (X ^ 2 - 16) := by
  rw [clearedF, control_cleared_matrix, det_cycle_pair]
  ring

#print axioms Paper7Control44.control_cleared_factorization

/-- Cancel only the nonzero polynomial prefactor in the proved cleared identity. -/
theorem control_sg_graphPhi :
    graphPhi (SG 4 controlP controlQ) =
      X ^ 2 * (X ^ 2 - 1) ^ 19 * (X ^ 2 - 9) * (X ^ 2 - 16) := by
  have hp : totalP 4 controlP = 0 := by
    norm_num [totalP, controlP, Fin.sum_univ_succ]
  have hq : totalQ 4 controlQ = 20 := by
    norm_num [totalQ, controlQ, Fin.sum_univ_succ]
  have hidentity := Paper7Cleared.cleared_identity 4 controlP controlQ (by decide)
  rw [hp, hq, control_cleared_factorization] at hidentity
  simp only [pow_zero, one_mul] at hidentity
  have hnonzero : (X ^ 4 * (X ^ 2 - 1) ^ 4 : Polynomial ℤ) ≠ 0 :=
    (Paper7Cleared.monic_denominator_factor 4 4).ne_zero
  apply mul_left_cancel₀ hnonzero
  calc
    (X ^ 4 * (X ^ 2 - 1) ^ 4) * graphPhi (SG 4 controlP controlQ) =
        (X ^ 2 - 1) ^ 20 *
          (X ^ 6 * (X ^ 2 - 1) ^ 3 * (X ^ 2 - 9) * (X ^ 2 - 16)) :=
      hidentity.symm
    _ = (X ^ 4 * (X ^ 2 - 1) ^ 4) *
        (X ^ 2 * (X ^ 2 - 1) ^ 19 * (X ^ 2 - 9) * (X ^ 2 - 16)) :=
      cleared_control_reassociation X (X ^ 2 - 1) (X ^ 2 - 9) (X ^ 2 - 16)

#print axioms Paper7Control44.control_sg_graphPhi

/-- The final polynomial concerns precisely the frozen sunGraph, without a replacement graph. -/
theorem control_graphPhi :
    graphPhi (sunGraph 4 C42Ten) =
      X ^ 2 * (X ^ 2 - 1) ^ 19 * (X ^ 2 - 9) * (X ^ 2 - 16) := by
  exact (congrArg
    (fun L : Fin 4 → List ℕ => graphPhi (sunGraph 4 L))
    control_parameters).symm.trans control_sg_graphPhi

#print axioms Paper7Control44.control_graphPhi

end Paper7Control44
