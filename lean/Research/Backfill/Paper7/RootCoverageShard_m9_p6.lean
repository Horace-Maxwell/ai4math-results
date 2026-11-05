import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_m9_p6 : prunedRootCheck candidateRows [-9, 6] 6 (6) = true := by
  exact prunedRootCheck_prune candidateRows [-9, 6] 4 (6) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m9_p6

end Paper7CycleThreeCertificate
