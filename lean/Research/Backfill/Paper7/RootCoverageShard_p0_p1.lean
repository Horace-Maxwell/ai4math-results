import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_p0_p1 : prunedRootCheck candidateRows [0, 1] 6 (1) = true := by
  exact prunedRootCheck_prune candidateRows [0, 1] 4 (1) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_p0_p1

end Paper7CycleThreeCertificate
