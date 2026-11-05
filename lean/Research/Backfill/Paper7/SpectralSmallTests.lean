import Research.Backfill.Paper7.BoundaryTestRequirements

/-! Root's uncompiled source candidate for tests 076--083.
Only small semantic tests are proved here; no paper contract is assumed. -/
set_option autoImplicit false
open scoped Classical
noncomputable section
namespace BackfillPaper7.StatementTestsV3
open Polynomial BackfillPaper7.Challenge

private theorem swap_charpoly {R : Type*} [CommRing R] [Nontrivial R] :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R).charpoly =
      (X - C (1 : R)) * (X - C (-1 : R)) := by
  simp [Matrix.charpoly_fin_two, Matrix.trace, Fin.sum_univ_succ, Matrix.det_fin_two]
  ring

private theorem c4_charpoly {R : Type*} [CommRing R] [Nontrivial R] :
    ((SimpleGraph.cycleGraph 4).adjMatrix R).charpoly =
      (X - C (2 : R)) * (X - C (-2 : R)) * X ^ 2 := by
  have hm : Matrix.charmatrix ((SimpleGraph.cycleGraph 4).adjMatrix R) =
      (!![X, -1, 0, -1; -1, X, -1, 0; 0, -1, X, -1; -1, 0, -1, X] :
        Matrix (Fin 4) (Fin 4) R[X]) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.charmatrix_apply, Matrix.diagonal_apply,
        SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj'] <;> decide
  rw [Matrix.charpoly, hm, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, Polynomial.C_ofNat]
  ring

private theorem swap_eigs :
    eigs (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      ({1, -1} : Multiset ℝ) := by
  have hp : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).charpoly =
      (({1, -1} : Multiset ℝ).map fun r => X - C r).prod := by
    rw [swap_charpoly]
    simp
  rw [eigs, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem c4_spec : spec (SimpleGraph.cycleGraph 4) =
    ({2, -2, 0, 0} : Multiset ℝ) := by
  have hp : ((SimpleGraph.cycleGraph 4).adjMatrix ℝ).charpoly =
      (({2, -2, 0, 0} : Multiset ℝ).map fun r => X - C r).prod := by
    rw [c4_charpoly]
    simp
    ring
  rw [spec, eigs, hp, Polynomial.roots_multiset_prod_X_sub_C]

theorem test_076 : BackfillPaper7.BoundaryTestRequirements.test_076 := by
  have hm : (⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ = !![0,1;1,0] := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [SimpleGraph.adjMatrix_apply]
  change eigs ((⊤ : SimpleGraph (Fin 2)).adjMatrix ℝ) = _
  rw [hm]
  exact swap_eigs

theorem test_077 : BackfillPaper7.BoundaryTestRequirements.test_077 := swap_eigs

theorem test_078 : BackfillPaper7.BoundaryTestRequirements.test_078 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_078
  norm_num [nPos, nNeg, nZero, swap_eigs, Multiset.filter_singleton]

theorem test_079 : BackfillPaper7.BoundaryTestRequirements.test_079 := c4_spec

theorem test_080 : BackfillPaper7.BoundaryTestRequirements.test_080 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_080
  norm_num [Ngt, Nge, Nlt, Nle, c4_spec]

theorem test_081 : BackfillPaper7.BoundaryTestRequirements.test_081 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_081
  norm_num [mult, c4_spec]

theorem test_082 : BackfillPaper7.BoundaryTestRequirements.test_082 := by
  unfold BackfillPaper7.BoundaryTestRequirements.test_082
  norm_num [Bplus, bigEigs, S2, c4_spec, Multiset.filter_singleton]

theorem test_083 : BackfillPaper7.BoundaryTestRequirements.test_083 := by
  intro μ hμ
  have hp := (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hμ
  have hz : μ = 2 ∨ μ + 2 = 0 ∨ μ = 0 := by
    simpa [c4_charpoly, Polynomial.IsRoot.def, mul_eq_zero,
      sub_eq_zero, or_assoc] using hp
  rcases hz with h | h | h
  · exact ⟨2, by simpa using h⟩
  · exact ⟨-2, by linear_combination h⟩
  · exact ⟨0, by simpa using h⟩

end BackfillPaper7.StatementTestsV3

#print axioms BackfillPaper7.StatementTestsV3.test_076
#print axioms BackfillPaper7.StatementTestsV3.test_077
#print axioms BackfillPaper7.StatementTestsV3.test_078
#print axioms BackfillPaper7.StatementTestsV3.test_079
#print axioms BackfillPaper7.StatementTestsV3.test_080
#print axioms BackfillPaper7.StatementTestsV3.test_081
#print axioms BackfillPaper7.StatementTestsV3.test_082
#print axioms BackfillPaper7.StatementTestsV3.test_083
