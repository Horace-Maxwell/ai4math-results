import Research.Backfill.Paper7.ClaudeB6T408Q0
import Research.Backfill.Paper7.ClaudeB6T408Q1
import Research.Backfill.Paper7.ClaudeB6T408Q2
import Research.Backfill.Paper7.ClaudeB6T408Q3
import Research.Backfill.Paper7.ClaudeB6T408Q4
import Research.Backfill.Paper7.ClaudeB6T408Q5
import Research.Backfill.Paper7.ClaudeB6T408Q6
import Research.Backfill.Paper7.ClaudeB6T408Q7
import Research.Backfill.Paper7.ClaudeB6T408Q8
import Research.Backfill.Paper7.ClaudeB6T408Q9
import Research.Backfill.Paper7.ClaudeB6T408Q10
import Research.Backfill.Paper7.ClaudeB6T408Q11
import Research.Backfill.Paper7.ClaudeB6T408Q12
import Research.Backfill.Paper7.ClaudeB6T408Q13
import Research.Backfill.Paper7.ClaudeB6T408Q14
import Research.Backfill.Paper7.ClaudeB6T408Q15
import Research.Backfill.Paper7.ClaudeB6T408Q16
import Research.Backfill.Paper7.ClaudeB6T408Q17
import Research.Backfill.Paper7.ClaudeB6T408Q18
import Research.Backfill.Paper7.MomentB6ComputableKernel
import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Claude, 2026-11-03. Complete theta=408 fibre (catalogue entry (42,408)): the sum of the
19 kernel-certified Q-slices Q = 0..18 of the original product evaluator, which is the whole
range of b6StructuralProductFastEvalTotal. Declaration names follow Codex's draft so that the
catalogue collector can use them unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta408WholeValue : ℕ :=
  claudeB6T408Q0Value + claudeB6T408Q1Value + claudeB6T408Q2Value + claudeB6T408Q3Value + claudeB6T408Q4Value + claudeB6T408Q5Value + claudeB6T408Q6Value + claudeB6T408Q7Value + claudeB6T408Q8Value + claudeB6T408Q9Value + claudeB6T408Q10Value + claudeB6T408Q11Value + claudeB6T408Q12Value + claudeB6T408Q13Value + claudeB6T408Q14Value + claudeB6T408Q15Value + claudeB6T408Q16Value + claudeB6T408Q17Value + claudeB6T408Q18Value
#print axioms Paper7MomentCounts.b6Theta408WholeValue

theorem b6Theta408Whole_eval_checked :
    b6EvalTotal (42,408) = (b6Theta408WholeValue : ℤ) := by
  have htotal : b6StructuralProductFastEvalTotal (42,408) = b6EvalTotal (42,408) := by
    rw [b6StructuralProductFastEvalTotal_eq, b6StructuralSortedFastEvalTotal_eq,
      b6SortedFastEvalTotal_eq, b6W6FastEvalTotal_eq, b6W6EvalTotal_eq]
  rw [← htotal]
  unfold b6StructuralProductFastEvalTotal
  rw [b6StructuralRangeOffset_zero_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, claudeB6T408Q0_slice, claudeB6T408Q1_slice, claudeB6T408Q2_slice, claudeB6T408Q3_slice, claudeB6T408Q4_slice, claudeB6T408Q5_slice, claudeB6T408Q6_slice, claudeB6T408Q7_slice, claudeB6T408Q8_slice, claudeB6T408Q9_slice, claudeB6T408Q10_slice, claudeB6T408Q11_slice, claudeB6T408Q12_slice, claudeB6T408Q13_slice, claudeB6T408Q14_slice, claudeB6T408Q15_slice, claudeB6T408Q16_slice, claudeB6T408Q17_slice, claudeB6T408Q18_slice]
  simp only [b6Theta408WholeValue, Nat.cast_add]
#print axioms Paper7MomentCounts.b6Theta408Whole_eval_checked

theorem b6Theta408Whole_candB1_theta_ncard :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 408}.ncard = b6Theta408WholeValue := by
  have hm : (42,408) ∈ b6FeatureCatalog := by norm_num [b6FeatureCatalog]
  have h : ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 408}.ncard : ℤ) =
      (b6Theta408WholeValue : ℤ) :=
    (b6EvalTotal_eq_original_theta_ncard (42,408) hm).symm.trans b6Theta408Whole_eval_checked
  exact_mod_cast h
#print axioms Paper7MomentCounts.b6Theta408Whole_candB1_theta_ncard

theorem b6Theta408Whole_candD2_theta_ncard :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 408}.ncard = b6Theta408WholeValue := by
  rw [b6_candD2_theta_fibre_eq_candB1 408]
  exact b6Theta408Whole_candB1_theta_ncard
#print axioms Paper7MomentCounts.b6Theta408Whole_candD2_theta_ncard

end Paper7MomentCounts
