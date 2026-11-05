import Research.Backfill.Paper7.ClaudeB6T696Q0
import Research.Backfill.Paper7.ClaudeB6T696Q1
import Research.Backfill.Paper7.ClaudeB6T696Q2
import Research.Backfill.Paper7.ClaudeB6T696Q3
import Research.Backfill.Paper7.ClaudeB6T696Q4
import Research.Backfill.Paper7.ClaudeB6T696Q5
import Research.Backfill.Paper7.ClaudeB6T696Q6
import Research.Backfill.Paper7.ClaudeB6T696Q7
import Research.Backfill.Paper7.ClaudeB6T696Q8
import Research.Backfill.Paper7.ClaudeB6T696Q9
import Research.Backfill.Paper7.ClaudeB6T696Q10
import Research.Backfill.Paper7.ClaudeB6T696Q11
import Research.Backfill.Paper7.ClaudeB6T696Q12
import Research.Backfill.Paper7.ClaudeB6T696Q13
import Research.Backfill.Paper7.ClaudeB6T696Q14
import Research.Backfill.Paper7.ClaudeB6T696Q15
import Research.Backfill.Paper7.ClaudeB6T696Q16
import Research.Backfill.Paper7.ClaudeB6T696Q17
import Research.Backfill.Paper7.ClaudeB6T696Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=696 fibre (catalogue entry (42,696)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta696WholeValue : ℕ :=
  claudeB6T696Q0Value + claudeB6T696Q1Value + claudeB6T696Q2Value + claudeB6T696Q3Value + claudeB6T696Q4Value + claudeB6T696Q5Value + claudeB6T696Q6Value + claudeB6T696Q7Value + claudeB6T696Q8Value + claudeB6T696Q9Value + claudeB6T696Q10Value + claudeB6T696Q11Value + claudeB6T696Q12Value + claudeB6T696Q13Value + claudeB6T696Q14Value + claudeB6T696Q15Value + claudeB6T696Q16Value + claudeB6T696Q17Value + claudeB6T696Q18Value
#print axioms Paper7MomentCounts.b6Theta696WholeValue

theorem b6Theta696Whole_eval_checked :
    b6EvalTotal (42,696) = (b6Theta696WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (42,696) = b6EvalTotal (42,696) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T696Q0_slice, claudeB6T696Q1_slice, claudeB6T696Q2_slice, claudeB6T696Q3_slice, claudeB6T696Q4_slice, claudeB6T696Q5_slice, claudeB6T696Q6_slice, claudeB6T696Q7_slice, claudeB6T696Q8_slice, claudeB6T696Q9_slice, claudeB6T696Q10_slice, claudeB6T696Q11_slice, claudeB6T696Q12_slice, claudeB6T696Q13_slice, claudeB6T696Q14_slice, claudeB6T696Q15_slice, claudeB6T696Q16_slice, claudeB6T696Q17_slice, claudeB6T696Q18_slice]
  simp only [b6Theta696WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta696Whole_eval_checked

theorem b6Theta696Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 696}.ncard = b6Theta696WholeValue := by
  have hm : (42,696) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 696}.ncard : ℤ) =
      (b6Theta696WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (42,696) hm).symm.trans b6Theta696Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta696Whole_candB1_theta_ncard

theorem b6Theta696Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 696}.ncard = b6Theta696WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 696]
  exact b6Theta696Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta696Whole_candD2_theta_ncard

end Paper7MomentCounts
