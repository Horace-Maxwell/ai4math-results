import Research.Backfill.Paper7.ClaudeB6T624Q0
import Research.Backfill.Paper7.ClaudeB6T624Q1
import Research.Backfill.Paper7.ClaudeB6T624Q2
import Research.Backfill.Paper7.ClaudeB6T624Q3
import Research.Backfill.Paper7.ClaudeB6T624Q4
import Research.Backfill.Paper7.ClaudeB6T624Q5
import Research.Backfill.Paper7.ClaudeB6T624Q6
import Research.Backfill.Paper7.ClaudeB6T624Q7
import Research.Backfill.Paper7.ClaudeB6T624Q8
import Research.Backfill.Paper7.ClaudeB6T624Q9
import Research.Backfill.Paper7.ClaudeB6T624Q10
import Research.Backfill.Paper7.ClaudeB6T624Q11
import Research.Backfill.Paper7.ClaudeB6T624Q12
import Research.Backfill.Paper7.ClaudeB6T624Q13
import Research.Backfill.Paper7.ClaudeB6T624Q14
import Research.Backfill.Paper7.ClaudeB6T624Q15
import Research.Backfill.Paper7.ClaudeB6T624Q16
import Research.Backfill.Paper7.ClaudeB6T624Q17
import Research.Backfill.Paper7.ClaudeB6T624Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=624 fibre (catalogue entry (33,624)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta624WholeValue : ℕ :=
  claudeB6T624Q0Value + claudeB6T624Q1Value + claudeB6T624Q2Value + claudeB6T624Q3Value + claudeB6T624Q4Value + claudeB6T624Q5Value + claudeB6T624Q6Value + claudeB6T624Q7Value + claudeB6T624Q8Value + claudeB6T624Q9Value + claudeB6T624Q10Value + claudeB6T624Q11Value + claudeB6T624Q12Value + claudeB6T624Q13Value + claudeB6T624Q14Value + claudeB6T624Q15Value + claudeB6T624Q16Value + claudeB6T624Q17Value + claudeB6T624Q18Value
#print axioms Paper7MomentCounts.b6Theta624WholeValue

theorem b6Theta624Whole_eval_checked :
    b6EvalTotal (33,624) = (b6Theta624WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (33,624) = b6EvalTotal (33,624) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T624Q0_slice, claudeB6T624Q1_slice, claudeB6T624Q2_slice, claudeB6T624Q3_slice, claudeB6T624Q4_slice, claudeB6T624Q5_slice, claudeB6T624Q6_slice, claudeB6T624Q7_slice, claudeB6T624Q8_slice, claudeB6T624Q9_slice, claudeB6T624Q10_slice, claudeB6T624Q11_slice, claudeB6T624Q12_slice, claudeB6T624Q13_slice, claudeB6T624Q14_slice, claudeB6T624Q15_slice, claudeB6T624Q16_slice, claudeB6T624Q17_slice, claudeB6T624Q18_slice]
  simp only [b6Theta624WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta624Whole_eval_checked

theorem b6Theta624Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 624}.ncard = b6Theta624WholeValue := by
  have hm : (33,624) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 624}.ncard : ℤ) =
      (b6Theta624WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (33,624) hm).symm.trans b6Theta624Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta624Whole_candB1_theta_ncard

theorem b6Theta624Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 624}.ncard = b6Theta624WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 624]
  exact b6Theta624Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta624Whole_candD2_theta_ncard

end Paper7MomentCounts
