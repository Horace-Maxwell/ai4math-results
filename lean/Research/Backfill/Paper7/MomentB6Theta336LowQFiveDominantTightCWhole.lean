import Research.Backfill.Paper7.ClaudeB6T336Q0
import Research.Backfill.Paper7.ClaudeB6T336Q1
import Research.Backfill.Paper7.ClaudeB6T336Q2
import Research.Backfill.Paper7.ClaudeB6T336Q3
import Research.Backfill.Paper7.ClaudeB6T336Q4
import Research.Backfill.Paper7.ClaudeB6T336Q5
import Research.Backfill.Paper7.ClaudeB6T336Q6
import Research.Backfill.Paper7.ClaudeB6T336Q7
import Research.Backfill.Paper7.ClaudeB6T336Q8
import Research.Backfill.Paper7.ClaudeB6T336Q9
import Research.Backfill.Paper7.ClaudeB6T336Q10
import Research.Backfill.Paper7.ClaudeB6T336Q11
import Research.Backfill.Paper7.ClaudeB6T336Q12
import Research.Backfill.Paper7.ClaudeB6T336Q13
import Research.Backfill.Paper7.ClaudeB6T336Q14
import Research.Backfill.Paper7.ClaudeB6T336Q15
import Research.Backfill.Paper7.ClaudeB6T336Q16
import Research.Backfill.Paper7.ClaudeB6T336Q17
import Research.Backfill.Paper7.ClaudeB6T336Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=336 fibre (catalogue entry (33,336)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta336WholeValue : ℕ :=
  claudeB6T336Q0Value + claudeB6T336Q1Value + claudeB6T336Q2Value + claudeB6T336Q3Value + claudeB6T336Q4Value + claudeB6T336Q5Value + claudeB6T336Q6Value + claudeB6T336Q7Value + claudeB6T336Q8Value + claudeB6T336Q9Value + claudeB6T336Q10Value + claudeB6T336Q11Value + claudeB6T336Q12Value + claudeB6T336Q13Value + claudeB6T336Q14Value + claudeB6T336Q15Value + claudeB6T336Q16Value + claudeB6T336Q17Value + claudeB6T336Q18Value
#print axioms Paper7MomentCounts.b6Theta336WholeValue

theorem b6Theta336Whole_eval_checked :
    b6EvalTotal (33,336) = (b6Theta336WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (33,336) = b6EvalTotal (33,336) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T336Q0_slice, claudeB6T336Q1_slice, claudeB6T336Q2_slice, claudeB6T336Q3_slice, claudeB6T336Q4_slice, claudeB6T336Q5_slice, claudeB6T336Q6_slice, claudeB6T336Q7_slice, claudeB6T336Q8_slice, claudeB6T336Q9_slice, claudeB6T336Q10_slice, claudeB6T336Q11_slice, claudeB6T336Q12_slice, claudeB6T336Q13_slice, claudeB6T336Q14_slice, claudeB6T336Q15_slice, claudeB6T336Q16_slice, claudeB6T336Q17_slice, claudeB6T336Q18_slice]
  simp only [b6Theta336WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta336Whole_eval_checked

theorem b6Theta336Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 336}.ncard = b6Theta336WholeValue := by
  have hm : (33,336) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 336}.ncard : ℤ) =
      (b6Theta336WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (33,336) hm).symm.trans b6Theta336Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta336Whole_candB1_theta_ncard

theorem b6Theta336Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 336}.ncard = b6Theta336WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 336]
  exact b6Theta336Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta336Whole_candD2_theta_ncard

end Paper7MomentCounts
