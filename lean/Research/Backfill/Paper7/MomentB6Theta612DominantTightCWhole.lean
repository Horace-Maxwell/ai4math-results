import Research.Backfill.Paper7.ClaudeB6T612Q0
import Research.Backfill.Paper7.ClaudeB6T612Q1
import Research.Backfill.Paper7.ClaudeB6T612Q2
import Research.Backfill.Paper7.ClaudeB6T612Q3
import Research.Backfill.Paper7.ClaudeB6T612Q4
import Research.Backfill.Paper7.ClaudeB6T612Q5
import Research.Backfill.Paper7.ClaudeB6T612Q6
import Research.Backfill.Paper7.ClaudeB6T612Q7
import Research.Backfill.Paper7.ClaudeB6T612Q8
import Research.Backfill.Paper7.ClaudeB6T612Q9
import Research.Backfill.Paper7.ClaudeB6T612Q10
import Research.Backfill.Paper7.ClaudeB6T612Q11
import Research.Backfill.Paper7.ClaudeB6T612Q12
import Research.Backfill.Paper7.ClaudeB6T612Q13
import Research.Backfill.Paper7.ClaudeB6T612Q14
import Research.Backfill.Paper7.ClaudeB6T612Q15
import Research.Backfill.Paper7.ClaudeB6T612Q16
import Research.Backfill.Paper7.ClaudeB6T612Q17
import Research.Backfill.Paper7.ClaudeB6T612Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=612 fibre (catalogue entry (29,612)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta612WholeValue : ℕ :=
  claudeB6T612Q0Value + claudeB6T612Q1Value + claudeB6T612Q2Value + claudeB6T612Q3Value + claudeB6T612Q4Value + claudeB6T612Q5Value + claudeB6T612Q6Value + claudeB6T612Q7Value + claudeB6T612Q8Value + claudeB6T612Q9Value + claudeB6T612Q10Value + claudeB6T612Q11Value + claudeB6T612Q12Value + claudeB6T612Q13Value + claudeB6T612Q14Value + claudeB6T612Q15Value + claudeB6T612Q16Value + claudeB6T612Q17Value + claudeB6T612Q18Value
#print axioms Paper7MomentCounts.b6Theta612WholeValue

theorem b6Theta612Whole_eval_checked :
    b6EvalTotal (29,612) = (b6Theta612WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (29,612) = b6EvalTotal (29,612) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T612Q0_slice, claudeB6T612Q1_slice, claudeB6T612Q2_slice, claudeB6T612Q3_slice, claudeB6T612Q4_slice, claudeB6T612Q5_slice, claudeB6T612Q6_slice, claudeB6T612Q7_slice, claudeB6T612Q8_slice, claudeB6T612Q9_slice, claudeB6T612Q10_slice, claudeB6T612Q11_slice, claudeB6T612Q12_slice, claudeB6T612Q13_slice, claudeB6T612Q14_slice, claudeB6T612Q15_slice, claudeB6T612Q16_slice, claudeB6T612Q17_slice, claudeB6T612Q18_slice]
  simp only [b6Theta612WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta612Whole_eval_checked

theorem b6Theta612Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 612}.ncard = b6Theta612WholeValue := by
  have hm : (29,612) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 612}.ncard : ℤ) =
      (b6Theta612WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (29,612) hm).symm.trans b6Theta612Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta612Whole_candB1_theta_ncard

theorem b6Theta612Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 612}.ncard = b6Theta612WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 612]
  exact b6Theta612Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta612Whole_candD2_theta_ncard

end Paper7MomentCounts
