import Research.Backfill.Paper7.MomentB6Theta312Q0To4
import Research.Backfill.Paper7.MomentB6Theta312Q4To8
import Research.Backfill.Paper7.MomentB6Theta312Q8To12
import Research.Backfill.Paper7.MomentB6Theta312Q12To16
import Research.Backfill.Paper7.MomentB6Theta312Q16To19

/-! Uncompiled whole original theta312 wrapper, preserving the original four heads.
All19Q are covered by five complete disjoint Ico segments. WholeValue is the sum
of their future certified values; the proof uses finite-sum concatenation and
prunedTotal=originalTotal. It does not repeat whole-total numerical reduction.
Original B1/D2 filtered-set ncard conclusions and limits are unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta312WholeValue : ℕ :=
  b6Theta312Q0To4Value + b6Theta312Q4To8Value + b6Theta312Q8To12Value + b6Theta312Q12To16Value + b6Theta312Q16To19Value
#print axioms Paper7MomentCounts.b6Theta312WholeValue
#print Paper7MomentCounts.b6Theta312WholeValue

theorem b6Theta312Whole_eval_checked :
    b6EvalTotal (25,312) = (b6Theta312WholeValue : ℤ) := by
  have hs : b6ArithmeticPrunedTotal (25,312) =
      b6Theta312Q0To4Expr +
      b6Theta312Q4To8Expr +
      b6Theta312Q8To12Expr +
      b6Theta312Q12To16Expr +
      b6Theta312Q16To19Expr := by
    let f : ℕ → ℤ := fun Q =>
        ∑ Z ∈ b6EvalZRange (25,312) Q,
          bif b6EvalCatalogAccept (25,312) Z Q then
            ∑ A ∈ Finset.range (Z+1),
              ∑ B ∈ b6EvalBRange Z (b6EvalResidual (25,312) Z Q) A,
                bif (b6EvalTripleGuard A B &&
                    b6EvalTripleGuard (Z-A) (b6EvalResidual (25,312) Z Q-B)) then
                  ∑ t ∈ b6EvalQSplitRange Z A Q,
                    b6ArithmeticPrunedKernel A B t *
                      b6ArithmeticPrunedKernel (Z-A) (b6EvalResidual (25,312) Z Q-B) (Q-t)
                else 0
          else 0
    change (∑ Q ∈ Finset.range 19, f Q) =
      (∑ Q ∈ Finset.Ico 0 4, f Q) + (∑ Q ∈ Finset.Ico 4 8, f Q) +
        (∑ Q ∈ Finset.Ico 8 12, f Q) + (∑ Q ∈ Finset.Ico 12 16, f Q) +
        (∑ Q ∈ Finset.Ico 16 19, f Q)
    symm
    rw [Finset.sum_Ico_consecutive f
      (show (0 : ℕ) ≤ 4 by omega) (show (4 : ℕ) ≤ 8 by omega)]
    rw [Finset.sum_Ico_consecutive f
      (show (0 : ℕ) ≤ 8 by omega) (show (8 : ℕ) ≤ 12 by omega)]
    rw [Finset.sum_Ico_consecutive f
      (show (0 : ℕ) ≤ 12 by omega) (show (12 : ℕ) ≤ 16 by omega)]
    rw [Finset.sum_Ico_consecutive f
      (show (0 : ℕ) ≤ 16 by omega) (show (16 : ℕ) ≤ 19 by omega)]
    rw [Nat.Ico_zero_eq_range]
  rw [← b6ArithmeticPrunedTotal_eq (25,312),hs,
    b6Theta312Q0To4_checked,
    b6Theta312Q4To8_checked,
    b6Theta312Q8To12_checked,
    b6Theta312Q12To16_checked,
    b6Theta312Q16To19_checked]
  change (b6Theta312Q0To4Value : ℤ) + (b6Theta312Q4To8Value : ℤ) + (b6Theta312Q8To12Value : ℤ) + (b6Theta312Q12To16Value : ℤ) + (b6Theta312Q16To19Value : ℤ) =
    ((b6Theta312Q0To4Value + b6Theta312Q4To8Value + b6Theta312Q8To12Value + b6Theta312Q12To16Value + b6Theta312Q16To19Value : ℕ) : ℤ)
  simp only [Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta312Whole_eval_checked

theorem b6Theta312Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 312}.ncard = b6Theta312WholeValue := by
  have hm : (25,312) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 312}.ncard : ℤ) =
      (b6Theta312WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (25,312) hm).symm.trans b6Theta312Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta312Whole_candB1_theta_ncard

theorem b6Theta312Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 312}.ncard = b6Theta312WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 312]
  exact b6Theta312Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta312Whole_candD2_theta_ncard

end Paper7MomentCounts
