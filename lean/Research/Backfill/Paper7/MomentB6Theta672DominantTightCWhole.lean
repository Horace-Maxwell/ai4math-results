import Research.Backfill.Paper7.ClaudeB6T672Q0
import Research.Backfill.Paper7.ClaudeB6T672Q1
import Research.Backfill.Paper7.ClaudeB6T672Q2
import Research.Backfill.Paper7.ClaudeB6T672Q3
import Research.Backfill.Paper7.ClaudeB6T672Q4
import Research.Backfill.Paper7.ClaudeB6T672Q5
import Research.Backfill.Paper7.ClaudeB6T672Q6
import Research.Backfill.Paper7.ClaudeB6T672Q7
import Research.Backfill.Paper7.ClaudeB6T672Q8
import Research.Backfill.Paper7.ClaudeB6T672Q9
import Research.Backfill.Paper7.ClaudeB6T672Q10
import Research.Backfill.Paper7.ClaudeB6T672Q11
import Research.Backfill.Paper7.ClaudeB6T672Q12
import Research.Backfill.Paper7.ClaudeB6T672Q13
import Research.Backfill.Paper7.ClaudeB6T672Q14
import Research.Backfill.Paper7.ClaudeB6T672Q15
import Research.Backfill.Paper7.ClaudeB6T672Q16
import Research.Backfill.Paper7.ClaudeB6T672Q17
import Research.Backfill.Paper7.ClaudeB6T672Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=672 fibre (catalogue entry (34,672)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta672WholeValue : ℕ :=
  claudeB6T672Q0Value + claudeB6T672Q1Value + claudeB6T672Q2Value + claudeB6T672Q3Value + claudeB6T672Q4Value + claudeB6T672Q5Value + claudeB6T672Q6Value + claudeB6T672Q7Value + claudeB6T672Q8Value + claudeB6T672Q9Value + claudeB6T672Q10Value + claudeB6T672Q11Value + claudeB6T672Q12Value + claudeB6T672Q13Value + claudeB6T672Q14Value + claudeB6T672Q15Value + claudeB6T672Q16Value + claudeB6T672Q17Value + claudeB6T672Q18Value
#print axioms Paper7MomentCounts.b6Theta672WholeValue

theorem b6Theta672Whole_eval_checked :
    b6EvalTotal (34,672) = (b6Theta672WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (34,672) = b6EvalTotal (34,672) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T672Q0_slice, claudeB6T672Q1_slice, claudeB6T672Q2_slice, claudeB6T672Q3_slice, claudeB6T672Q4_slice, claudeB6T672Q5_slice, claudeB6T672Q6_slice, claudeB6T672Q7_slice, claudeB6T672Q8_slice, claudeB6T672Q9_slice, claudeB6T672Q10_slice, claudeB6T672Q11_slice, claudeB6T672Q12_slice, claudeB6T672Q13_slice, claudeB6T672Q14_slice, claudeB6T672Q15_slice, claudeB6T672Q16_slice, claudeB6T672Q17_slice, claudeB6T672Q18_slice]
  simp only [b6Theta672WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta672Whole_eval_checked

theorem b6Theta672Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 672}.ncard = b6Theta672WholeValue := by
  have hm : (34,672) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 672}.ncard : ℤ) =
      (b6Theta672WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (34,672) hm).symm.trans b6Theta672Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta672Whole_candB1_theta_ncard

theorem b6Theta672Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 672}.ncard = b6Theta672WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 672]
  exact b6Theta672Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta672Whole_candD2_theta_ncard

end Paper7MomentCounts
