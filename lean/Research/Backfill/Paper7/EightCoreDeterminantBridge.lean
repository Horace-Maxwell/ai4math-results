import Research.Backfill.Paper7.AlgebraicContracts
import Research.Backfill.Paper7.EightCoreMatrixAlgebra

/-! Keep the dimension symbolic while unfolding the determinant definitions.
The concrete eight-cycle proof uses these named polynomial functions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open Polynomial BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

def finCoreDet (b : ℕ) (M : Matrix (Fin b) (Fin b) (Polynomial ℤ)) : Polynomial ℤ :=
  M.det
#print axioms Paper7EightCycle.finCoreDet

theorem finCoreDet_eq_det (b : ℕ) (M : Matrix (Fin b) (Fin b) (Polynomial ℤ)) :
    finCoreDet b M = M.det := rfl
#print axioms Paper7EightCycle.finCoreDet_eq_det

theorem clearedF_eq_finCoreDet (b : ℕ) (p q : Fin b → ℕ) :
    clearedF b p q = finCoreDet b (clearedMatrix b p q) := rfl
#print axioms Paper7EightCycle.clearedF_eq_finCoreDet

theorem finCoreDet_of_smul_eq (b : ℕ)
    (A B : Matrix (Fin b) (Fin b) (Polynomial ℤ)) (s : Polynomial ℤ)
    (h : A = s • B) : finCoreDet b A = s^b*finCoreDet b B := by
  exact eight_core_det_of_smul_eq A B s b (Fintype.card_fin b) h
#print axioms Paper7EightCycle.finCoreDet_of_smul_eq

theorem clearedF_of_smul_eq (b : ℕ) (p q : Fin b → ℕ)
    (B : Matrix (Fin b) (Fin b) (Polynomial ℤ)) (s : Polynomial ℤ)
    (h : clearedMatrix b p q = s • B) :
    clearedF b p q = s^b*finCoreDet b B :=
  (clearedF_eq_finCoreDet b p q).trans
    (finCoreDet_of_smul_eq b (clearedMatrix b p q) B s h)
#print axioms Paper7EightCycle.clearedF_of_smul_eq

end Paper7EightCycle
