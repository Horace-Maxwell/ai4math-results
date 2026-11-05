import Research.Backfill.Paper7.ClaudeB6T840Q0
import Research.Backfill.Paper7.ClaudeB6T840Q1
import Research.Backfill.Paper7.ClaudeB6T840Q2
import Research.Backfill.Paper7.ClaudeB6T840Q3
import Research.Backfill.Paper7.ClaudeB6T840Q4
import Research.Backfill.Paper7.ClaudeB6T840Q5
import Research.Backfill.Paper7.ClaudeB6T840Q6
import Research.Backfill.Paper7.ClaudeB6T840Q7
import Research.Backfill.Paper7.ClaudeB6T840Q8
import Research.Backfill.Paper7.ClaudeB6T840Q9
import Research.Backfill.Paper7.ClaudeB6T840Q10
import Research.Backfill.Paper7.ClaudeB6T840Q11
import Research.Backfill.Paper7.ClaudeB6T840Q12
import Research.Backfill.Paper7.ClaudeB6T840Q13
import Research.Backfill.Paper7.ClaudeB6T840Q14
import Research.Backfill.Paper7.ClaudeB6T840Q15
import Research.Backfill.Paper7.ClaudeB6T840Q16
import Research.Backfill.Paper7.ClaudeB6T840Q17
import Research.Backfill.Paper7.ClaudeB6T840Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=840 fibre (catalogue entry (41,840)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta840WholeValue : ℕ :=
  claudeB6T840Q0Value + claudeB6T840Q1Value + claudeB6T840Q2Value + claudeB6T840Q3Value + claudeB6T840Q4Value + claudeB6T840Q5Value + claudeB6T840Q6Value + claudeB6T840Q7Value + claudeB6T840Q8Value + claudeB6T840Q9Value + claudeB6T840Q10Value + claudeB6T840Q11Value + claudeB6T840Q12Value + claudeB6T840Q13Value + claudeB6T840Q14Value + claudeB6T840Q15Value + claudeB6T840Q16Value + claudeB6T840Q17Value + claudeB6T840Q18Value
#print axioms Paper7MomentCounts.b6Theta840WholeValue

theorem b6Theta840Whole_eval_checked :
    b6EvalTotal (41,840) = (b6Theta840WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (41,840) = b6EvalTotal (41,840) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T840Q0_slice, claudeB6T840Q1_slice, claudeB6T840Q2_slice, claudeB6T840Q3_slice, claudeB6T840Q4_slice, claudeB6T840Q5_slice, claudeB6T840Q6_slice, claudeB6T840Q7_slice, claudeB6T840Q8_slice, claudeB6T840Q9_slice, claudeB6T840Q10_slice, claudeB6T840Q11_slice, claudeB6T840Q12_slice, claudeB6T840Q13_slice, claudeB6T840Q14_slice, claudeB6T840Q15_slice, claudeB6T840Q16_slice, claudeB6T840Q17_slice, claudeB6T840Q18_slice]
  simp only [b6Theta840WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta840Whole_eval_checked

theorem b6Theta840Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 840}.ncard = b6Theta840WholeValue := by
  have hm : (41,840) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 840}.ncard : ℤ) =
      (b6Theta840WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (41,840) hm).symm.trans b6Theta840Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta840Whole_candB1_theta_ncard

theorem b6Theta840Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 840}.ncard = b6Theta840WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 840]
  exact b6Theta840Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta840Whole_candD2_theta_ncard

end Paper7MomentCounts
