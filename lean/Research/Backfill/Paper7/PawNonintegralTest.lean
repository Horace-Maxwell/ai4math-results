import Research.Backfill.Paper7.BoundaryTestRequirements

/-! The triangle with one leaf has a noninteger eigenvalue in (2,3).
This test uses its actual four vertices and adjacency matrix, not BMS or any
unproved paper contract. -/
set_option autoImplicit false
namespace Paper7StatementTestsV3
open BackfillPaper7.Challenge Polynomial

abbrev PawV := SunV 3 ![[1], [], []]

def pawEquiv : Fin 4 ≃ PawV where
  toFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 2,
    Sum.inr ⟨0, ⟨0, by decide⟩, ⟨0, by decide⟩⟩]
  invFun := fun
    | Sum.inl k => k.castSucc
    | Sum.inr _ => 3
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    rintro (k | ⟨k,j,t⟩)
    · fin_cases k <;> rfl
    · fin_cases k <;> fin_cases j
      fin_cases t
      rfl
#print axioms Paper7StatementTestsV3.pawEquiv

theorem paw_reindex :
    Matrix.reindex pawEquiv.symm pawEquiv.symm
      ((sunGraph 3 ![[1], [], []]).adjMatrix ℂ) =
        !![0,1,1,1; 1,0,1,0; 1,1,0,0; 1,0,0,0] := by
  rw [Matrix.reindex_apply]
  ext i j
  change ((sunGraph 3 ![[1], [], []]).adjMatrix ℂ) (pawEquiv i) (pawEquiv j) =
    (!![0,1,1,1; 1,0,1,0; 1,1,0,0; 1,0,0,0] : Matrix (Fin 4) (Fin 4) ℂ) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pawEquiv, SimpleGraph.adjMatrix, sunGraph,
      SimpleGraph.fromRel_adj, sunRel]
#print axioms Paper7StatementTestsV3.paw_reindex

theorem paw_charpoly_complex :
    ((sunGraph 3 ![[1], [], []]).adjMatrix ℂ).charpoly =
      (X+1)*(X^3-X^2-3*X+1) := by
  rw [← Matrix.charpoly_reindex pawEquiv.symm, paw_reindex]
  have hm : Matrix.charmatrix
      (!![0,1,1,1; 1,0,1,0; 1,1,0,0; 1,0,0,0] : Matrix (Fin 4) (Fin 4) ℂ) =
      (!![X,-1,-1,-1; -1,X,-1,0; -1,-1,X,0; -1,0,0,X] :
        Matrix (Fin 4) (Fin 4) (Polynomial ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.charmatrix_apply, Matrix.diagonal_apply]
  rw [Matrix.charpoly, hm, Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, Polynomial.C_ofNat]
  ring
#print axioms Paper7StatementTestsV3.paw_charpoly_complex

theorem test075 : BackfillPaper7.BoundaryTestRequirements.test_075 := by
  intro hint
  let f : ℝ → ℝ := fun x => x^3-x^2-3*x+1
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hzero : (0 : ℝ) ∈ Set.Ioo (f 2) (f 3) := by norm_num [f]
  obtain ⟨r,hr,heval⟩ := intermediate_value_Ioo (by norm_num : (2 : ℝ) ≤ 3)
    hcont.continuousOn hzero
  have hreal : r^3-r^2-3*r+1 = 0 := heval
  have hcomplex : (r : ℂ)^3-(r : ℂ)^2-3*(r : ℂ)+1 = 0 := by exact_mod_cast hreal
  have hroot : Polynomial.IsRoot ((sunGraph 3 ![[1], [], []]).adjMatrix ℂ).charpoly
      (r : ℂ) := by
    rw [paw_charpoly_complex]
    simp only [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
      Polynomial.eval_ofNat]
    rw [hcomplex, mul_zero]
  obtain ⟨z,hz⟩ := hint _ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot)
  have hrz : r = (z : ℝ) := by simpa using congrArg Complex.re hz
  rw [hrz] at hr
  have hlo : (2 : ℤ) < z := by exact_mod_cast hr.1
  have hhi : z < (3 : ℤ) := by exact_mod_cast hr.2
  omega
#print axioms Paper7StatementTestsV3.test075

end Paper7StatementTestsV3
