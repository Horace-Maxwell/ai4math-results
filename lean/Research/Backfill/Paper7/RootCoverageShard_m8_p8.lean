import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_m8_p8 : prunedRootCheck candidateRows [-8, 8] 6 (8) = true := by
  exact prunedRootCheck_prune candidateRows [-8, 8] 4 (8) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m8_p8

end Paper7CycleThreeCertificate
