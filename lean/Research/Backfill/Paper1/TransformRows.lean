import Research.Backfill.Paper1.PathAndSign
import Research.Backfill.Paper1.SupplementStatements

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1
namespace NarrowTransform

lemma entry_symm (k : ℕ) (x : ℝ) (i j : ℕ) :
    Challenge.tEntry k x i j = Challenge.tEntry k x j i := by
  unfold Challenge.tEntry
  split_ifs <;> first | rfl | omega | (congr 2; omega)

end NarrowTransform

theorem check_TransformRows : NarrowSupplement.TransformRows := by
  intro x hx k _hk
  constructor
  · intro i _hi j _hj
    exact NarrowTransform.entry_symm k x i j
  · intro i hi
    rw [Additional.tMulVec_eq_Tv x k (fun _ => 1) i hi]
    exact ICGGeneral.Tv_one (by linarith) k i hi

#print axioms check_TransformRows
end CodexPaper1
