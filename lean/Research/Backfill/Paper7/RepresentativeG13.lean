import Research.Backfill.Paper7.ThreeRepresentativesBridge

/-! Complete order, pendant positivity and integer charpoly of the frozen G13. -/

set_option autoImplicit false
open scoped Matrix

namespace Paper7ThreeRepresentatives

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

abbrev g13P : Fin 4 → ℕ := ![6,0,3,0]
#print axioms Paper7ThreeRepresentatives.g13P

abbrev g13Q : Fin 4 → ℕ := ![0,0,0,0]
#print axioms Paper7ThreeRepresentatives.g13Q

theorem g13_parameters : pq 4 g13P g13Q = G13 := by
  funext i
  fin_cases i <;> rfl

#print axioms Paper7ThreeRepresentatives.g13_parameters

theorem g13_order : order 4 G13 = 13 := by
  have h := Paper7Setup.sg_order 4 g13P g13Q
  have hn : nOf 4 g13P g13Q = 13 := by
    norm_num [nOf, g13P, g13Q, Fin.sum_univ_succ]
  rw [hn] at h
  simpa only [g13_parameters] using h

#print axioms Paper7ThreeRepresentatives.g13_order

theorem g13_pendant_positive : 0 < pendantCount 4 G13 := by
  norm_num [pendantCount, G13, Fin.sum_univ_succ]

#print axioms Paper7ThreeRepresentatives.g13_pendant_positive

theorem g13_cleared_matrix :
    clearedMatrix 4 g13P g13Q =
      (!![(X^2-1)*(X^2-6), -X*(X^2-1), 0, -X*(X^2-1);
          -X*(X^2-1), X^2*(X^2-1), -X*(X^2-1), 0;
          0, -X*(X^2-1), (X^2-1)*(X^2-3), -X*(X^2-1);
          -X*(X^2-1), 0, -X*(X^2-1), X^2*(X^2-1)] :
        Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedMatrix, cycle_adjacency_four, g13P, g13Q] <;> ring

#print axioms Paper7ThreeRepresentatives.g13_cleared_matrix

theorem g13_cleared_factorization :
    clearedF 4 g13P g13Q =
      X ^ 4 * (X ^ 2 - 1) ^ 4 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
  rw [clearedF, g13_cleared_matrix, det_cycle_diagonal]
  ring

#print axioms Paper7ThreeRepresentatives.g13_cleared_factorization

theorem g13_graphPhi :
    graphPhi (sunGraph 4 G13) = X ^ 9 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
  have hp : totalP 4 g13P = 9 := by
    norm_num [totalP, g13P, Fin.sum_univ_succ]
  have hq : totalQ 4 g13Q = 0 := by
    norm_num [totalQ, g13Q, Fin.sum_univ_succ]
  have hphi : graphPhi (SG 4 g13P g13Q) =
      X ^ 9 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
    apply graphPhi_of_cleared_four g13P g13Q
    rw [hp, hq, g13_cleared_factorization]
    simp only [pow_zero, mul_one]
    exact reassociate_g13 X (X ^ 2 - 1) (X ^ 2 - 4) (X ^ 2 - 9)
  exact (congrArg
    (fun L : Fin 4 → List ℕ => graphPhi (sunGraph 4 L))
    g13_parameters).symm.trans hphi

#print axioms Paper7ThreeRepresentatives.g13_graphPhi

end Paper7ThreeRepresentatives
