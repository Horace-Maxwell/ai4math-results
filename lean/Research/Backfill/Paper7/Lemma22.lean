import Research.Backfill.Paper7.ZeroGapCount
import Research.Backfill.Paper7.SmatMonodromyEquivalence

/-! Complete original frozen Lemma22 proof candidate. Every gap cover, direct
product, parity count and bound is supplied by actual proof bodies in the
selected dependency chain. This source has not been compiled or accepted. -/
set_option autoImplicit false
noncomputable section

namespace Paper7Lemma22
open BackfillPaper7.Challenge
open Paper7Lemma22Gaps

theorem check_Lemma22 : BackfillPaper7.Challenge.Lemma22 := by
  intro b p q hb
  refine ⟨Paper7Lemma22Periodic.lemma22_ordinary_clause b p q hb,
    lemma22_zero_clause b p q hb, ?_, lemma22_maximum_bounds b p q hb⟩
  intro ε hε
  refine ⟨sign_offset_real b p q hb ε hε, ?_, ?_⟩
  · intro hK
    exact ⟨deltaE_eq_sum_gapDim b p q ε hK,
      fun k hk => gapDim_le_one b p q hb ε k hk⟩
  · intro hK
    exact deltaE_empty_bound b p q hb ε hK
#print axioms Paper7Lemma22.check_Lemma22

end Paper7Lemma22
