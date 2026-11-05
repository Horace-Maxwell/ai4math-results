import Research.Backfill.Paper7.SunBlockDefinitions

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Paper7Cleared

/-- An explicit inverse candidate, used below only for t = 1 or t = 2. -/
def pathInverse {K : Type*} [Field K] (x : K) (t : ℕ) : Matrix (Fin t) (Fin t) K :=
  fun i j => if t = 1 then (if i = j then x⁻¹ else 0)
    else if i = j then x / (x ^ 2 - 1) else 1 / (x ^ 2 - 1)

#print axioms Paper7Cleared.pathInverse

theorem pathShift_det {K : Type*} [CommRing K] (x : K) (t : ℕ)
    (ht : t = 1 ∨ t = 2) :
    (pathShift x t).det = if t = 1 then x else x ^ 2 - 1 := by
  rcases ht with rfl | rfl
  · simp [pathShift]
  · norm_num [Matrix.det_fin_two, pathShift]
    all_goals ring

#print axioms Paper7Cleared.pathShift_det

theorem pathInverse_mul_shift {K : Type*} [Field K] (x : K) (t : ℕ)
    (ht : t = 1 ∨ t = 2) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    pathInverse x t * pathShift x t = 1 := by
  rcases ht with rfl | rfl
  · ext i j
    fin_cases i
    fin_cases j
    simp [pathInverse, pathShift, Matrix.mul_apply, hx]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pathInverse, pathShift, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals field_simp [hquad]
    all_goals ring

#print axioms Paper7Cleared.pathInverse_mul_shift

theorem pathShift_mul_inverse {K : Type*} [Field K] (x : K) (t : ℕ)
    (ht : t = 1 ∨ t = 2) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    pathShift x t * pathInverse x t = 1 := by
  rcases ht with rfl | rfl
  · ext i j
    fin_cases i
    fin_cases j
    simp [pathInverse, pathShift, Matrix.mul_apply, hx]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pathInverse, pathShift, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals field_simp [hquad]
    all_goals ring

#print axioms Paper7Cleared.pathShift_mul_inverse

theorem pathShift_nonsing_inverse {K : Type*} [Field K] (x : K) (t : ℕ)
    (ht : t = 1 ∨ t = 2) (hx : x ≠ 0) (hquad : x ^ 2 - 1 ≠ 0) :
    (pathShift x t)⁻¹ = pathInverse x t := by
  apply Matrix.inv_eq_left_inv
  exact pathInverse_mul_shift x t ht hx hquad

#print axioms Paper7Cleared.pathShift_nonsing_inverse

theorem pathInverse_diagonal {K : Type*} [Field K] (x : K) (t : ℕ) (i : Fin t) :
    pathInverse x t i i = if t = 1 then x⁻¹ else x / (x ^ 2 - 1) := by
  simp [pathInverse]

#print axioms Paper7Cleared.pathInverse_diagonal

end Paper7Cleared
