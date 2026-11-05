import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_m3_p2 : prunedRootCheck candidateRows [-3, 2] 6 (2) = true := by
  exact prunedRootCheck_prune candidateRows [-3, 2] 4 (2) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_p2

end Paper7CycleThreeCertificate
