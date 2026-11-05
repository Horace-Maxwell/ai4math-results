import Research.Backfill.Paper7.ClaudeB6T396Q0
import Research.Backfill.Paper7.ClaudeB6T396Q1
import Research.Backfill.Paper7.ClaudeB6T396Q2
import Research.Backfill.Paper7.ClaudeB6T396Q3
import Research.Backfill.Paper7.ClaudeB6T396Q4
import Research.Backfill.Paper7.ClaudeB6T396Q5
import Research.Backfill.Paper7.ClaudeB6T396Q6
import Research.Backfill.Paper7.ClaudeB6T396Q7
import Research.Backfill.Paper7.ClaudeB6T396Q8
import Research.Backfill.Paper7.ClaudeB6T396Q9
import Research.Backfill.Paper7.ClaudeB6T396Q10
import Research.Backfill.Paper7.ClaudeB6T396Q11
import Research.Backfill.Paper7.ClaudeB6T396Q12
import Research.Backfill.Paper7.ClaudeB6T396Q13
import Research.Backfill.Paper7.ClaudeB6T396Q14
import Research.Backfill.Paper7.ClaudeB6T396Q15
import Research.Backfill.Paper7.ClaudeB6T396Q16
import Research.Backfill.Paper7.ClaudeB6T396Q17
import Research.Backfill.Paper7.ClaudeB6T396Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=396 fibre (catalogue entry (38,396)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta396WholeValue : ℕ :=
  claudeB6T396Q0Value + claudeB6T396Q1Value + claudeB6T396Q2Value + claudeB6T396Q3Value + claudeB6T396Q4Value + claudeB6T396Q5Value + claudeB6T396Q6Value + claudeB6T396Q7Value + claudeB6T396Q8Value + claudeB6T396Q9Value + claudeB6T396Q10Value + claudeB6T396Q11Value + claudeB6T396Q12Value + claudeB6T396Q13Value + claudeB6T396Q14Value + claudeB6T396Q15Value + claudeB6T396Q16Value + claudeB6T396Q17Value + claudeB6T396Q18Value
#print axioms Paper7MomentCounts.b6Theta396WholeValue

theorem b6Theta396Whole_eval_checked :
    b6EvalTotal (38,396) = (b6Theta396WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (38,396) = b6EvalTotal (38,396) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T396Q0_slice, claudeB6T396Q1_slice, claudeB6T396Q2_slice, claudeB6T396Q3_slice, claudeB6T396Q4_slice, claudeB6T396Q5_slice, claudeB6T396Q6_slice, claudeB6T396Q7_slice, claudeB6T396Q8_slice, claudeB6T396Q9_slice, claudeB6T396Q10_slice, claudeB6T396Q11_slice, claudeB6T396Q12_slice, claudeB6T396Q13_slice, claudeB6T396Q14_slice, claudeB6T396Q15_slice, claudeB6T396Q16_slice, claudeB6T396Q17_slice, claudeB6T396Q18_slice]
  simp only [b6Theta396WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta396Whole_eval_checked

theorem b6Theta396Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 396}.ncard = b6Theta396WholeValue := by
  have hm : (38,396) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 396}.ncard : ℤ) =
      (b6Theta396WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (38,396) hm).symm.trans b6Theta396Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta396Whole_candB1_theta_ncard

theorem b6Theta396Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 396}.ncard = b6Theta396WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 396]
  exact b6Theta396Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta396Whole_candD2_theta_ncard

end Paper7MomentCounts
