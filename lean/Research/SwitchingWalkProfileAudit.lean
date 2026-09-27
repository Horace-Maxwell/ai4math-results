import Research.SwitchingWalkProfile

/-! Audit file for `Research.SwitchingWalkProfile`: prints the final statements and the key
definition, and checks the semantics of `switchVec` on small examples. -/

set_option autoImplicit false

open Matrix

#print SwitchingWalkProfile.switchVec
#check @SwitchingWalkProfile.annihilator
#check @SwitchingWalkProfile.eigen_nonorth
#check @SwitchingWalkProfile.main_after_switching
#check @SwitchingWalkProfile.walkRegular_main_after_switching

-- semantics of the switching vector s_v = 1 - 2 e_v
example : SwitchingWalkProfile.switchVec (1 : Fin 3) 1 = -1 := by
  simp [SwitchingWalkProfile.switchVec]
example : SwitchingWalkProfile.switchVec (1 : Fin 3) 0 = 1 := by
  simp [SwitchingWalkProfile.switchVec]
-- `D_s A D_s` really flips the signs of the edges at `v`: for the triangle K_3 switched at 0,
-- the entry (0,1) becomes -1 and the entry (1,2) stays 1.
example : (diagonal (SwitchingWalkProfile.switchVec (0 : Fin 3)) *
    (!![0, 1, 1; 1, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ) *
    diagonal (SwitchingWalkProfile.switchVec (0 : Fin 3))) 0 1 = -1 := by
  simp [SwitchingWalkProfile.switchVec, Matrix.mul_apply, Fin.sum_univ_three, diagonal]
example : (diagonal (SwitchingWalkProfile.switchVec (0 : Fin 3)) *
    (!![0, 1, 1; 1, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ) *
    diagonal (SwitchingWalkProfile.switchVec (0 : Fin 3))) 1 2 = 1 := by
  simp [SwitchingWalkProfile.switchVec, Matrix.mul_apply, Fin.sum_univ_three, diagonal]

#print axioms SwitchingWalkProfile.annihilator
#print axioms SwitchingWalkProfile.eigen_nonorth
#print axioms SwitchingWalkProfile.main_after_switching
#print axioms SwitchingWalkProfile.walkRegular_main_after_switching
