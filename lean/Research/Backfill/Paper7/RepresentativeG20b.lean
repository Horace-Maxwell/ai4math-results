import Research.Backfill.Paper7.ThreeRepresentativesBridge

/-! Complete order, pendant positivity and integer charpoly of the frozen G20b. -/

set_option autoImplicit false
open scoped Matrix

namespace Paper7ThreeRepresentatives

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

abbrev g20bP : Fin 4 → ℕ := ![0,0,0,0]
#print axioms Paper7ThreeRepresentatives.g20bP

abbrev g20bQ : Fin 4 → ℕ := ![4,4,0,0]
#print axioms Paper7ThreeRepresentatives.g20bQ

theorem g20b_parameters : pq 4 g20bP g20bQ = G20b := by
  funext i
  fin_cases i <;> rfl

#print axioms Paper7ThreeRepresentatives.g20b_parameters

theorem g20b_order : order 4 G20b = 20 := by
  have h := Paper7Setup.sg_order 4 g20bP g20bQ
  have hn : nOf 4 g20bP g20bQ = 20 := by
    norm_num [nOf, g20bP, g20bQ, Fin.sum_univ_succ]
  rw [hn] at h
  simpa only [g20b_parameters] using h

#print axioms Paper7ThreeRepresentatives.g20b_order

theorem g20b_pendant_positive : 0 < pendantCount 4 G20b := by
  norm_num [pendantCount, G20b, Fin.sum_univ_succ]

#print axioms Paper7ThreeRepresentatives.g20b_pendant_positive

theorem g20b_cleared_matrix :
    clearedMatrix 4 g20bP g20bQ =
      (!![X^2*(X^2-5), -X*(X^2-1), 0, -X*(X^2-1);
          -X*(X^2-1), X^2*(X^2-5), -X*(X^2-1), 0;
          0, -X*(X^2-1), X^2*(X^2-1), -X*(X^2-1);
          -X*(X^2-1), 0, -X*(X^2-1), X^2*(X^2-1)] :
        Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedMatrix, cycle_adjacency_four, g20bP, g20bQ] <;> ring

#print axioms Paper7ThreeRepresentatives.g20b_cleared_matrix

theorem g20b_cleared_factorization :
    clearedF 4 g20bP g20bQ =
      X ^ 6 * (X ^ 2 - 1) ^ 3 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
  rw [clearedF, g20b_cleared_matrix, det_cycle_diagonal]
  ring

#print axioms Paper7ThreeRepresentatives.g20b_cleared_factorization

theorem g20b_graphPhi :
    graphPhi (sunGraph 4 G20b) =
      X ^ 2 * (X ^ 2 - 1) ^ 7 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
  have hp : totalP 4 g20bP = 0 := by
    norm_num [totalP, g20bP, Fin.sum_univ_succ]
  have hq : totalQ 4 g20bQ = 8 := by
    norm_num [totalQ, g20bQ, Fin.sum_univ_succ]
  have hphi : graphPhi (SG 4 g20bP g20bQ) =
      X ^ 2 * (X ^ 2 - 1) ^ 7 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
    apply graphPhi_of_cleared_four g20bP g20bQ
    rw [hp, hq, g20b_cleared_factorization]
    simp only [pow_zero, one_mul]
    exact reassociate_g20b X (X ^ 2 - 1) (X ^ 2 - 4) (X ^ 2 - 9)
  exact (congrArg
    (fun L : Fin 4 → List ℕ => graphPhi (sunGraph 4 L))
    g20b_parameters).symm.trans hphi

#print axioms Paper7ThreeRepresentatives.g20b_graphPhi

end Paper7ThreeRepresentatives
