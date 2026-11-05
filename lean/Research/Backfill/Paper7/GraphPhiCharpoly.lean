import Research.Backfill.Paper7.AlgebraicContracts

set_option autoImplicit false

namespace Paper7GraphPhi

open BackfillPaper7.Challenge.Legacy.Algebra

theorem graphPhi_eq_charpoly {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphPhi G = (G.adjMatrix ℤ).charpoly := by
  unfold graphPhi
  apply congrArg Matrix.charpoly
  ext u v
  by_cases h : G.Adj u v <;> simp [SimpleGraph.adjMatrix_apply, h]

#print axioms Paper7GraphPhi.graphPhi_eq_charpoly

end Paper7GraphPhi
