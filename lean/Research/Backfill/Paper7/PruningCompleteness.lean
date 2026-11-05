import Research.Backfill.Paper7.IntegralLeafCompleteness
import Research.Backfill.Paper7.PruningFiniteStage
import Research.Backfill.Paper7.PruningSpectrumStage
import Research.Backfill.Paper7.PruningMonotone

/-! Source-only assembly of the original eleven-conjunct frozen contract.
Every imported candidate has an explicit proof body and remains uncompiled.
No statement of search, DP or canonical correctness is added as a hypothesis. -/
set_option autoImplicit false
namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open Paper7PruningSpectrum Paper7PruningGuards

theorem check_PruningAndEnumerationCompleteness :
    BackfillPaper7.Challenge.Legacy.PruningAndEnumerationCompleteness := by
  refine ⟨admissible_has_pareto_maximal, enumerated_eq_budget,
    pruning_actual_spectrum_encoding, amonotone_downward, pruning_windowPass,
    reachD1_iff, reachD2_iff, ?_, integral_has_leaf, ?_, integral_iff_certified_orbit⟩
  · intro load cyc b N d _hb he hbN hN hd x hx
    exact dReachable_completion_iff load cyc b N d he hbN hN hd x hx
  · intro v b N _hdom x
    exact certifiedOutputs_iff v b N x
#print axioms Paper7Pruning.check_PruningAndEnumerationCompleteness

end Paper7Pruning
