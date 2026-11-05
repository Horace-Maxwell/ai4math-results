import Research.Backfill.Paper7.ThreeRepresentativesBridge

/-! Complete order, pendant positivity and integer charpoly of the frozen G20a. -/

set_option autoImplicit false
open scoped Matrix

namespace Paper7ThreeRepresentatives

open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

abbrev g20aP : Fin 4 → ℕ := ![0,1,0,1]
#print axioms Paper7ThreeRepresentatives.g20aP

abbrev g20aQ : Fin 4 → ℕ := ![5,0,2,0]
#print axioms Paper7ThreeRepresentatives.g20aQ

theorem g20a_parameters : pq 4 g20aP g20aQ = G20a := by
  funext i
  fin_cases i <;> rfl

#print axioms Paper7ThreeRepresentatives.g20a_parameters

theorem g20a_order : order 4 G20a = 20 := by
  have h := Paper7Setup.sg_order 4 g20aP g20aQ
  have hn : nOf 4 g20aP g20aQ = 20 := by
    norm_num [nOf, g20aP, g20aQ, Fin.sum_univ_succ]
  rw [hn] at h
  simpa only [g20a_parameters] using h

#print axioms Paper7ThreeRepresentatives.g20a_order

theorem g20a_pendant_positive : 0 < pendantCount 4 G20a := by
  norm_num [pendantCount, G20a, Fin.sum_univ_succ]

#print axioms Paper7ThreeRepresentatives.g20a_pendant_positive

theorem g20a_cleared_matrix :
    clearedMatrix 4 g20aP g20aQ =
      (!![X^2*(X^2-6), -X*(X^2-1), 0, -X*(X^2-1);
          -X*(X^2-1), (X^2-1)^2, -X*(X^2-1), 0;
          0, -X*(X^2-1), X^2*(X^2-3), -X*(X^2-1);
          -X*(X^2-1), 0, -X*(X^2-1), (X^2-1)^2] :
        Matrix (Fin 4) (Fin 4) (Polynomial ℤ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [clearedMatrix, cycle_adjacency_four, g20aP, g20aQ] <;> ring

#print axioms Paper7ThreeRepresentatives.g20a_cleared_matrix

theorem g20a_cleared_factorization :
    clearedF 4 g20aP g20aQ =
      X ^ 4 * (X ^ 2 - 1) ^ 4 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
  rw [clearedF, g20a_cleared_matrix, det_cycle_diagonal]
  ring

#print axioms Paper7ThreeRepresentatives.g20a_cleared_factorization

theorem g20a_graphPhi :
    graphPhi (sunGraph 4 G20a) =
      X ^ 2 * (X ^ 2 - 1) ^ 7 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
  have hp : totalP 4 g20aP = 2 := by
    norm_num [totalP, g20aP, Fin.sum_univ_succ]
  have hq : totalQ 4 g20aQ = 7 := by
    norm_num [totalQ, g20aQ, Fin.sum_univ_succ]
  have hphi : graphPhi (SG 4 g20aP g20aQ) =
      X ^ 2 * (X ^ 2 - 1) ^ 7 * (X ^ 2 - 4) * (X ^ 2 - 9) := by
    apply graphPhi_of_cleared_four g20aP g20aQ
    rw [hp, hq, g20a_cleared_factorization]
    exact reassociate_g20a X (X ^ 2 - 1) (X ^ 2 - 4) (X ^ 2 - 9)
  exact (congrArg
    (fun L : Fin 4 → List ℕ => graphPhi (sunGraph 4 L))
    g20a_parameters).symm.trans hphi

#print axioms Paper7ThreeRepresentatives.g20a_graphPhi

end Paper7ThreeRepresentatives
