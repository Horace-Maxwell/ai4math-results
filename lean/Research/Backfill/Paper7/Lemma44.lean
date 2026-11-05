import Research.Backfill.Paper7.RankSigmaBounds

/-! Complete frozen Lemma44 candidate, with all six original conjuncts. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Rank
open BackfillPaper7.Challenge

theorem check_Lemma44 : BackfillPaper7.Challenge.Lemma44 := by
  intro b p q hb hpos hG
  refine ⟨rank_identity b p q hb hG, rank_lower b p q hb hpos hG,
    rank_sigma_bound b p q hb hG, ?_, ?_, ?_⟩
  · exact rank_sigma_nonempty b p q hb hG
  · exact rank_sigma_empty b p q hb hG
  · exact cycle_length_le_thirteen b p q hb hpos hG
#print axioms Paper7Rank.check_Lemma44

end Paper7Rank
