import Research.Backfill.Paper7.ClaudeB6T684Q0
import Research.Backfill.Paper7.ClaudeB6T684Q1
import Research.Backfill.Paper7.ClaudeB6T684Q2
import Research.Backfill.Paper7.ClaudeB6T684Q3
import Research.Backfill.Paper7.ClaudeB6T684Q4
import Research.Backfill.Paper7.ClaudeB6T684Q5
import Research.Backfill.Paper7.ClaudeB6T684Q6
import Research.Backfill.Paper7.ClaudeB6T684Q7
import Research.Backfill.Paper7.ClaudeB6T684Q8
import Research.Backfill.Paper7.ClaudeB6T684Q9
import Research.Backfill.Paper7.ClaudeB6T684Q10
import Research.Backfill.Paper7.ClaudeB6T684Q11
import Research.Backfill.Paper7.ClaudeB6T684Q12
import Research.Backfill.Paper7.ClaudeB6T684Q13
import Research.Backfill.Paper7.ClaudeB6T684Q14
import Research.Backfill.Paper7.ClaudeB6T684Q15
import Research.Backfill.Paper7.ClaudeB6T684Q16
import Research.Backfill.Paper7.ClaudeB6T684Q17
import Research.Backfill.Paper7.ClaudeB6T684Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=684 fibre (catalogue entry (38,684)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta684WholeValue : ℕ :=
  claudeB6T684Q0Value + claudeB6T684Q1Value + claudeB6T684Q2Value + claudeB6T684Q3Value + claudeB6T684Q4Value + claudeB6T684Q5Value + claudeB6T684Q6Value + claudeB6T684Q7Value + claudeB6T684Q8Value + claudeB6T684Q9Value + claudeB6T684Q10Value + claudeB6T684Q11Value + claudeB6T684Q12Value + claudeB6T684Q13Value + claudeB6T684Q14Value + claudeB6T684Q15Value + claudeB6T684Q16Value + claudeB6T684Q17Value + claudeB6T684Q18Value
#print axioms Paper7MomentCounts.b6Theta684WholeValue

theorem b6Theta684Whole_eval_checked :
    b6EvalTotal (38,684) = (b6Theta684WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (38,684) = b6EvalTotal (38,684) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T684Q0_slice, claudeB6T684Q1_slice, claudeB6T684Q2_slice, claudeB6T684Q3_slice, claudeB6T684Q4_slice, claudeB6T684Q5_slice, claudeB6T684Q6_slice, claudeB6T684Q7_slice, claudeB6T684Q8_slice, claudeB6T684Q9_slice, claudeB6T684Q10_slice, claudeB6T684Q11_slice, claudeB6T684Q12_slice, claudeB6T684Q13_slice, claudeB6T684Q14_slice, claudeB6T684Q15_slice, claudeB6T684Q16_slice, claudeB6T684Q17_slice, claudeB6T684Q18_slice]
  simp only [b6Theta684WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta684Whole_eval_checked

theorem b6Theta684Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 684}.ncard = b6Theta684WholeValue := by
  have hm : (38,684) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 684}.ncard : ℤ) =
      (b6Theta684WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (38,684) hm).symm.trans b6Theta684Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta684Whole_candB1_theta_ncard

theorem b6Theta684Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 684}.ncard = b6Theta684WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 684]
  exact b6Theta684Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta684Whole_candD2_theta_ncard

end Paper7MomentCounts
