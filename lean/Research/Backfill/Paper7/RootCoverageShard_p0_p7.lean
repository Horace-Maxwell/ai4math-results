import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_p0_p7 : prunedRootCheck candidateRows [0, 7] 6 (7) = true := by
  exact prunedRootCheck_prune candidateRows [0, 7] 4 (7) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_p0_p7

end Paper7CycleThreeCertificate
