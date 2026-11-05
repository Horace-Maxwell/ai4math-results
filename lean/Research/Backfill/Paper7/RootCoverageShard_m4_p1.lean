import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.CandidateRootRows

/-! Generated UNCOMPILED obligations; no search result is trusted. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

theorem rootnode_m4_p1 : prunedRootCheck candidateRows [-4, 1] 6 (1) = true := by
  exact prunedRootCheck_prune candidateRows [-4, 1] 4 (1) (by decide +kernel)
#print axioms Paper7CycleThreeCertificate.rootnode_m4_p1

end Paper7CycleThreeCertificate
