import Research.Backfill.Paper7.MomentB6Theta264Q0To4
import Research.Backfill.Paper7.MomentB6Theta264Q4To8
import Research.Backfill.Paper7.MomentB6Theta264Q8To12
import Research.Backfill.Paper7.MomentB6Theta264Q12To16
import Research.Backfill.Paper7.MomentB6FirstQ18Certificate
import Research.Backfill.Paper7.MomentB6Theta264Q17Complete
import Research.Backfill.Paper7.MomentB6Theta264Q16Slice

/-! Uncompiled algebraic wrapper after actual930 whole-prefix timeout.
The original eight complete public headers are preserved. The unknown prefix
value is the sum of four independently certified complete Q intervals; no
Meta.reduce or all-prefix reflexivity evaluation is executed in this wrapper.
Exact Ico concatenation plus the three actual successful suffixes covers all
nineteen Q values and both original theta264 filtered-set ncard statements.
Default limits and linters remain unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta264RemainingPrefix : ℤ :=
  ∑ Q ∈ Finset.range 16, b6EvalQSlice (24,264) Q
#print axioms Paper7MomentCounts.b6Theta264RemainingPrefix

theorem b6Theta264_eval_total_split :
    b6EvalTotal (24,264) = b6Theta264RemainingPrefix +
      (b6Theta264Q16Value : ℤ) + (b6Theta264Q17Value : ℤ) +
      (b6Theta264Q18Value : ℤ) := by
  unfold b6EvalTotal b6Theta264RemainingPrefix
  rw [Finset.sum_range_succ (fun Q => b6EvalQSlice (24,264) Q) 18,
    Finset.sum_range_succ (fun Q => b6EvalQSlice (24,264) Q) 17,
    Finset.sum_range_succ (fun Q => b6EvalQSlice (24,264) Q) 16,
    b6EvalQSlice_eq (24,264) 16,b6Theta264Q16_original_QSlice_checked,
    b6EvalQSlice_eq (24,264) 17,b6Theta264Q17_original_QSlice_checked,
    b6Theta264Q18_QSlice_checked]
#print axioms Paper7MomentCounts.b6Theta264_eval_total_split

def b6Theta264RemainingPrefixValue : ℕ :=
  b6Theta264Q0To4Value + b6Theta264Q4To8Value + b6Theta264Q8To12Value + b6Theta264Q12To16Value
#print axioms Paper7MomentCounts.b6Theta264RemainingPrefixValue
#print Paper7MomentCounts.b6Theta264RemainingPrefixValue

theorem b6Theta264_remaining_prefix_checked :
    b6Theta264RemainingPrefix = (b6Theta264RemainingPrefixValue : ℤ) := by
  have hsplit : b6Theta264Q0To4Expr + b6Theta264Q4To8Expr +
      b6Theta264Q8To12Expr + b6Theta264Q12To16Expr = b6Theta264RemainingPrefix := by
    unfold b6Theta264Q0To4Expr b6Theta264Q4To8Expr b6Theta264Q8To12Expr
      b6Theta264Q12To16Expr b6Theta264RemainingPrefix
    rw [Finset.sum_Ico_consecutive (fun Q => b6EvalQSlice (24,264) Q)
      (show (0 : ℕ) ≤ 4 by omega) (show (4 : ℕ) ≤ 8 by omega)]
    rw [Finset.sum_Ico_consecutive (fun Q => b6EvalQSlice (24,264) Q)
      (show (0 : ℕ) ≤ 8 by omega) (show (8 : ℕ) ≤ 12 by omega)]
    rw [Finset.sum_Ico_consecutive (fun Q => b6EvalQSlice (24,264) Q)
      (show (0 : ℕ) ≤ 12 by omega) (show (12 : ℕ) ≤ 16 by omega)]
    rw [Nat.Ico_zero_eq_range]
  calc
    b6Theta264RemainingPrefix = b6Theta264Q0To4Expr + b6Theta264Q4To8Expr +
        b6Theta264Q8To12Expr + b6Theta264Q12To16Expr := hsplit.symm
    _ = (b6Theta264Q0To4Value : ℤ) + (b6Theta264Q4To8Value : ℤ) +
        (b6Theta264Q8To12Value : ℤ) + (b6Theta264Q12To16Value : ℤ) := by
      rw [b6Theta264Q0To4_checked,b6Theta264Q4To8_checked,
        b6Theta264Q8To12_checked,b6Theta264Q12To16_checked]
    _ = (b6Theta264RemainingPrefixValue : ℤ) := by
      change (b6Theta264Q0To4Value : ℤ) + (b6Theta264Q4To8Value : ℤ) +
          (b6Theta264Q8To12Value : ℤ) + (b6Theta264Q12To16Value : ℤ) =
        ((b6Theta264Q0To4Value + b6Theta264Q4To8Value +
          b6Theta264Q8To12Value + b6Theta264Q12To16Value : ℕ) : ℤ)
      simp only [Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta264_remaining_prefix_checked

def b6Theta264Value : ℕ :=
  b6Theta264RemainingPrefixValue + b6Theta264Q16Value + b6Theta264Q17Value + b6Theta264Q18Value
#print axioms Paper7MomentCounts.b6Theta264Value
#print Paper7MomentCounts.b6Theta264Value

theorem b6Theta264_eval_total_checked :
    b6EvalTotal (24,264) = (b6Theta264Value : ℤ) := by
  rw [b6Theta264_eval_total_split,b6Theta264_remaining_prefix_checked]
  change (b6Theta264RemainingPrefixValue : ℤ) + (b6Theta264Q16Value : ℤ) +
      (b6Theta264Q17Value : ℤ) + (b6Theta264Q18Value : ℤ) =
    ((b6Theta264RemainingPrefixValue + b6Theta264Q16Value +
      b6Theta264Q17Value + b6Theta264Q18Value : ℕ) : ℤ)
  simp only [Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta264_eval_total_checked

theorem b6Theta264_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 264}.ncard = b6Theta264Value := by
  have hm : (24,264) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 264}.ncard : ℤ) =
      (b6Theta264Value : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (24,264) hm).symm.trans b6Theta264_eval_total_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta264_candB1_theta_ncard

theorem b6Theta264_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 264}.ncard = b6Theta264Value := by
  rw [b6_candD2_theta_fibre_eq_candB1 264]
  exact b6Theta264_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta264_candD2_theta_ncard

end Paper7MomentCounts
