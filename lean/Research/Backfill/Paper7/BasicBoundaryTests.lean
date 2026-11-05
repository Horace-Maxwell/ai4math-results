import Research.Backfill.Paper7.BoundaryTestRequirements

/-! Exact small finite controls. All computations remain Lean kernel obligations. -/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Paper7StatementTestsV3
open BackfillPaper7.Challenge

theorem test084 : BackfillPaper7.BoundaryTestRequirements.test_084 := by
  norm_num [BackfillPaper7.BoundaryTestRequirements.test_084, Matrix.trace,
    pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, SimpleGraph.adjMatrix_apply]
#print axioms Paper7StatementTestsV3.test084

theorem test093 : BackfillPaper7.BoundaryTestRequirements.test_093 := by
  norm_num [BackfillPaper7.BoundaryTestRequirements.test_093, Matrix.trace,
    pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, SimpleGraph.adjMatrix_apply,
    SimpleGraph.pathGraph_adj]
#print axioms Paper7StatementTestsV3.test093

theorem test094 : BackfillPaper7.BoundaryTestRequirements.test_094 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_094
  decide +kernel
#print axioms Paper7StatementTestsV3.test094

theorem test095 : BackfillPaper7.BoundaryTestRequirements.test_095 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_095
  decide +kernel
#print axioms Paper7StatementTestsV3.test095

theorem test096 : BackfillPaper7.BoundaryTestRequirements.test_096 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_096
  decide +kernel
#print axioms Paper7StatementTestsV3.test096

theorem test097 : BackfillPaper7.BoundaryTestRequirements.test_097 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_097
  decide +kernel
#print axioms Paper7StatementTestsV3.test097

theorem test098 : BackfillPaper7.BoundaryTestRequirements.test_098 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_098
  decide +kernel
#print axioms Paper7StatementTestsV3.test098

theorem test099 : BackfillPaper7.BoundaryTestRequirements.test_099 := by
  refine ⟨id, Function.injective_id, ?_, ?_⟩
  · simp only [id_eq, SimpleGraph.pathGraph_adj]
    decide +kernel
  · simp only [id_eq, SimpleGraph.pathGraph_adj]
    decide +kernel
#print axioms Paper7StatementTestsV3.test099

theorem test100 : BackfillPaper7.BoundaryTestRequirements.test_100 := by
  rintro ⟨v,hinj,_,hlocal⟩
  have hne : v (3 : Fin 4) ≠ v 0 := by
    intro h
    have hindex := hinj h
    exact (by decide : (3 : Fin 4) ≠ 0) hindex
  have hadj : (⊤ : SimpleGraph (Fin 4)).Adj (v 3) (v 0) := by
    simpa using hne
  obtain ⟨j,hneighbor,heq⟩ := (hlocal 3 (by decide) (v 0)).mp hadj
  have hj : j = 0 := (hinj heq).symm
  subst j
  norm_num at hneighbor
#print axioms Paper7StatementTestsV3.test100

theorem test101 : BackfillPaper7.BoundaryTestRequirements.test_101 := by
  intro A q _
  simp [Matrix.trace]
#print axioms Paper7StatementTestsV3.test101

theorem test102 : BackfillPaper7.BoundaryTestRequirements.test_102 := by
  simp [BackfillPaper7.BoundaryTestRequirements.test_102, eigs]
#print axioms Paper7StatementTestsV3.test102

end Paper7StatementTestsV3
