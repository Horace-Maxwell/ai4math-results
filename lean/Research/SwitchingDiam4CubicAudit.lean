import Research.SwitchingDiam4Cubic

/-! Audit file for `Research.SwitchingDiam4Cubic`: prints the final statements and checks the
hypothesis format on a small example (a 1×1 symmetric matrix, whose only eigenvalue is its entry). -/

set_option autoImplicit false

open Matrix Polynomial

#check @SwitchingDiam4.no_eigenvalue_root_cubic
#check @SwitchingDiam4.no_rat_root
#check @SwitchingDiam4.real_root_unique

-- semantics of the hypothesis: for the 1×1 matrix `!![5]`, `θ = 5` is a root of the mapped charpoly
example : ((!![(5 : ℚ)]).map (algebraMap ℚ ℝ)).charpoly.eval 5 = 0 := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_unique]

-- and the lemma then says `5 ^ 3 - 5 + 2 ≠ 0`
example : (5 : ℝ) ^ 3 - 5 + 2 ≠ 0 :=
  SwitchingDiam4.no_eigenvalue_root_cubic (!![(5 : ℚ)]) (by ext i j; fin_cases i; fin_cases j; rfl) 5
    (by simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_unique])

#print axioms SwitchingDiam4.no_eigenvalue_root_cubic
#print axioms SwitchingDiam4.no_rat_root
#print axioms SwitchingDiam4.real_root_unique
