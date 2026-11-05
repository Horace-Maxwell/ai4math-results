import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_m3_p3 : prunedRootCheck candidateRows [-3, 3] 6 (3) = true := by
  exact prunedRootCheck_prune candidateRows [-3, 3] 4 (3) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_p3

end Paper7CycleThreeCertificate
