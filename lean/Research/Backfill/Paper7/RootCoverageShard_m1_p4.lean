import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_m1_p4 : prunedRootCheck candidateRows [-1, 4] 6 (4) = true := by
  exact prunedRootCheck_prune candidateRows [-1, 4] 4 (4) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m1_p4

end Paper7CycleThreeCertificate
