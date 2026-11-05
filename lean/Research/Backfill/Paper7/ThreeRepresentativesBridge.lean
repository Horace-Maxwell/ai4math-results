import Research.Backfill.Paper7.ClearedCharacteristicPolynomial
import Research.Backfill.Paper7.SetupCardinality

/-! Source-only four-cycle polynomial tools for the three named representatives.
The only mathematical dependencies are the bound, previously accepted sources.
This candidate has not been compiled or formally accepted. -/

set_option autoImplicit false
open scoped Matrix

namespace Paper7ThreeRepresentatives

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem cycle_adjacency_four :
    cycleAdjZ 4 = (!![0,1,0,1; 1,0,1,0; 0,1,0,1; 1,0,1,0] :
      Matrix (Fin 4) (Fin 4) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cycleAdjZ, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj'] <;>
    decide

#print axioms Paper7ThreeRepresentatives.cycle_adjacency_four

/-- The four diagonal entries remain in their actual cyclic order. -/
theorem det_cycle_diagonal {R : Type*} [CommRing R] (a b c d e : R) :
    (!![a,e,0,e; e,b,e,0; 0,e,c,e; e,0,e,d] : Matrix (Fin 4) (Fin 4) R).det =
      a * b * c * d - e ^ 2 * (a + c) * (b + d) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

#print axioms Paper7ThreeRepresentatives.det_cycle_diagonal

/-- Cancel the nonzero clearing factor over Polynomial Z, with no point exclusions. -/
theorem graphPhi_of_cleared_four (p q : Fin 4 → ℕ) (f : Polynomial ℤ)
    (hf : X ^ totalP 4 p * (X ^ 2 - 1) ^ totalQ 4 q * clearedF 4 p q =
      (X ^ 4 * (X ^ 2 - 1) ^ 4) * f) : graphPhi (SG 4 p q) = f := by
  have hid := Paper7Cleared.cleared_identity 4 p q (by decide)
  have hn : (X ^ 4 * (X ^ 2 - 1) ^ 4 : Polynomial ℤ) ≠ 0 :=
    (Paper7Cleared.monic_denominator_factor 4 4).ne_zero
  exact mul_left_cancel₀ hn (hid.symm.trans hf)

#print axioms Paper7ThreeRepresentatives.graphPhi_of_cleared_four

theorem reassociate_g13 {R : Type*} [CommRing R] (x y z t : R) :
    x ^ 9 * (x ^ 4 * y ^ 4 * z * t) =
      (x ^ 4 * y ^ 4) * (x ^ 9 * z * t) := by
  ring

#print axioms Paper7ThreeRepresentatives.reassociate_g13

theorem reassociate_g20a {R : Type*} [CommRing R] (x y z t : R) :
    x ^ 2 * y ^ 7 * (x ^ 4 * y ^ 4 * z * t) =
      (x ^ 4 * y ^ 4) * (x ^ 2 * y ^ 7 * z * t) := by
  ring

#print axioms Paper7ThreeRepresentatives.reassociate_g20a

theorem reassociate_g20b {R : Type*} [CommRing R] (x y z t : R) :
    y ^ 8 * (x ^ 6 * y ^ 3 * z * t) =
      (x ^ 4 * y ^ 4) * (x ^ 2 * y ^ 7 * z * t) := by
  ring

#print axioms Paper7ThreeRepresentatives.reassociate_g20b

end Paper7ThreeRepresentatives
