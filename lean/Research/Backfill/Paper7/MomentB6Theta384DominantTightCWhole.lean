import Research.Backfill.Paper7.ClaudeB6T384Q0
import Research.Backfill.Paper7.ClaudeB6T384Q1
import Research.Backfill.Paper7.ClaudeB6T384Q2
import Research.Backfill.Paper7.ClaudeB6T384Q3
import Research.Backfill.Paper7.ClaudeB6T384Q4
import Research.Backfill.Paper7.ClaudeB6T384Q5
import Research.Backfill.Paper7.ClaudeB6T384Q6
import Research.Backfill.Paper7.ClaudeB6T384Q7
import Research.Backfill.Paper7.ClaudeB6T384Q8
import Research.Backfill.Paper7.ClaudeB6T384Q9
import Research.Backfill.Paper7.ClaudeB6T384Q10
import Research.Backfill.Paper7.ClaudeB6T384Q11
import Research.Backfill.Paper7.ClaudeB6T384Q12
import Research.Backfill.Paper7.ClaudeB6T384Q13
import Research.Backfill.Paper7.ClaudeB6T384Q14
import Research.Backfill.Paper7.ClaudeB6T384Q15
import Research.Backfill.Paper7.ClaudeB6T384Q16
import Research.Backfill.Paper7.ClaudeB6T384Q17
import Research.Backfill.Paper7.ClaudeB6T384Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=384 fibre (catalogue entry (34,384)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta384WholeValue : ℕ :=
  claudeB6T384Q0Value + claudeB6T384Q1Value + claudeB6T384Q2Value + claudeB6T384Q3Value + claudeB6T384Q4Value + claudeB6T384Q5Value + claudeB6T384Q6Value + claudeB6T384Q7Value + claudeB6T384Q8Value + claudeB6T384Q9Value + claudeB6T384Q10Value + claudeB6T384Q11Value + claudeB6T384Q12Value + claudeB6T384Q13Value + claudeB6T384Q14Value + claudeB6T384Q15Value + claudeB6T384Q16Value + claudeB6T384Q17Value + claudeB6T384Q18Value
#print axioms Paper7MomentCounts.b6Theta384WholeValue

theorem b6Theta384Whole_eval_checked :
    b6EvalTotal (34,384) = (b6Theta384WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (34,384) = b6EvalTotal (34,384) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T384Q0_slice, claudeB6T384Q1_slice, claudeB6T384Q2_slice, claudeB6T384Q3_slice, claudeB6T384Q4_slice, claudeB6T384Q5_slice, claudeB6T384Q6_slice, claudeB6T384Q7_slice, claudeB6T384Q8_slice, claudeB6T384Q9_slice, claudeB6T384Q10_slice, claudeB6T384Q11_slice, claudeB6T384Q12_slice, claudeB6T384Q13_slice, claudeB6T384Q14_slice, claudeB6T384Q15_slice, claudeB6T384Q16_slice, claudeB6T384Q17_slice, claudeB6T384Q18_slice]
  simp only [b6Theta384WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta384Whole_eval_checked

theorem b6Theta384Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 384}.ncard = b6Theta384WholeValue := by
  have hm : (34,384) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 384}.ncard : ℤ) =
      (b6Theta384WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (34,384) hm).symm.trans b6Theta384Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta384Whole_candB1_theta_ncard

theorem b6Theta384Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 384}.ncard = b6Theta384WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 384]
  exact b6Theta384Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta384Whole_candD2_theta_ncard

end Paper7MomentCounts
