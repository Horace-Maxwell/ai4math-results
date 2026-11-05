import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_m3_p5 : prunedRootCheck candidateRows [-3, 5] 6 (5) = true := by
  exact prunedRootCheck_prune candidateRows [-3, 5] 4 (5) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m3_p5

end Paper7CycleThreeCertificate
