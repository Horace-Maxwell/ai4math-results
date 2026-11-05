import Research.Backfill.Paper7.MomentB6Theta324StructuralProductQ0To4
import Research.Backfill.Paper7.MomentB6Theta324ResidualPrunedQ4To8
import Research.Backfill.Paper7.MomentB6Theta324DominantTightCQ8To12
import Research.Backfill.Paper7.MomentB6Theta324DominantTightCQ12To16
import Research.Backfill.Paper7.MomentB6Theta324DominantTightCQ16To19

/-! SOURCE ONLY. Assemble the original complete five intervals Q[0,19).
The first two values are imported unchanged from successful actual977 and
actual985's successful prefix. The three remaining full-width intervals use
the same DominantTightC algorithm and their actual or still-pending Value defs.
The four complete original Whole headers and final B1/D2 proof bodies remain.
This wrapper only concatenates certified finite sums; it does not recompute
an entire theta or insert any guessed numeral. The two new suffixes still
need actual complete-source compile/checker success before this can be selected.
No failed Q8 module is imported, and no runtime plan or queue is created. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta324WholeValue : ℕ :=
  b6Theta324W6Q0To4Value + b6Theta324Q4To8Value + b6Theta324DominantTightCQ8To12Value + b6Theta324DominantTightCQ12To16Value + b6Theta324DominantTightCQ16To19Value
#print axioms Paper7MomentCounts.b6Theta324WholeValue
#print Paper7MomentCounts.b6Theta324WholeValue

theorem b6Theta324Whole_eval_checked :
    b6EvalTotal (29,324) = (b6Theta324WholeValue : ℤ) := by
  have hsplit :
      b6Theta324W6Q0To4Expr + b6Theta324Q4To8Expr + b6Theta324DominantTightCQ8To12Expr + b6Theta324DominantTightCQ12To16Expr + b6Theta324DominantTightCQ16To19Expr = b6StructuralProductFastEvalTotal (29,324) := by
    unfold b6Theta324W6Q0To4Expr b6Theta324Q4To8Expr b6Theta324DominantTightCQ8To12Expr b6Theta324DominantTightCQ12To16Expr b6Theta324DominantTightCQ16To19Expr b6StructuralProductFastEvalTotal
    simp only [b6StructuralDominantTightCResidualPrunedEvalQSlice_eq,
      b6StructuralTightCResidualPrunedEvalQSlice_eq,
      b6StructuralResidualPrunedEvalQSlice_eq,
      b6StructuralIcoSum_eq, b6StructuralRangeOffset_zero_eq]
    rw [Finset.sum_Ico_consecutive (fun Q => b6StructuralProductFastEvalQSlice (29,324) Q)
      (show (0 : ℕ) ≤ 4 by omega) (show (4 : ℕ) ≤ 8 by omega)]
    rw [Finset.sum_Ico_consecutive (fun Q => b6StructuralProductFastEvalQSlice (29,324) Q)
      (show (0 : ℕ) ≤ 8 by omega) (show (8 : ℕ) ≤ 12 by omega)]
    rw [Finset.sum_Ico_consecutive (fun Q => b6StructuralProductFastEvalQSlice (29,324) Q)
      (show (0 : ℕ) ≤ 12 by omega) (show (12 : ℕ) ≤ 16 by omega)]
    rw [Finset.sum_Ico_consecutive (fun Q => b6StructuralProductFastEvalQSlice (29,324) Q)
      (show (0 : ℕ) ≤ 16 by omega) (show (16 : ℕ) ≤ 19 by omega)]
    rw [Nat.Ico_zero_eq_range]
  have htotal : b6StructuralProductFastEvalTotal (29,324) = b6EvalTotal (29,324) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  calc
    b6EvalTotal (29,324) = b6StructuralProductFastEvalTotal (29,324) := htotal.symm
    _ = b6Theta324W6Q0To4Expr + b6Theta324Q4To8Expr + b6Theta324DominantTightCQ8To12Expr + b6Theta324DominantTightCQ12To16Expr + b6Theta324DominantTightCQ16To19Expr := hsplit.symm
    _ = (b6Theta324W6Q0To4Value : ℤ) + (b6Theta324Q4To8Value : ℤ) + (b6Theta324DominantTightCQ8To12Value : ℤ) + (b6Theta324DominantTightCQ12To16Value : ℤ) + (b6Theta324DominantTightCQ16To19Value : ℤ) := by
      rw [b6Theta324W6Q0To4_checked,b6Theta324Q4To8_checked,b6Theta324DominantTightCQ8To12_checked,b6Theta324DominantTightCQ12To16_checked,b6Theta324DominantTightCQ16To19_checked]
    _ = (b6Theta324WholeValue : ℤ) := by
      simp only [b6Theta324WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta324Whole_eval_checked

theorem b6Theta324Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 324}.ncard = b6Theta324WholeValue := by
  have hm : (29,324) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 324}.ncard : ℤ) =
      (b6Theta324WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (29,324) hm).symm.trans b6Theta324Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta324Whole_candB1_theta_ncard

theorem b6Theta324Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 324}.ncard = b6Theta324WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 324]
  exact b6Theta324Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta324Whole_candD2_theta_ncard

end Paper7MomentCounts
