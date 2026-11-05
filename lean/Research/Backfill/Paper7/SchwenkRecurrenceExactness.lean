import Research.Backfill.Paper7.EndpointSchurChain
import Research.Backfill.Paper7.SchwenkDetachedArms

/-! Exact original three-equality contract. The general unicyclic Schwenk
identity is neither imported as a theorem nor added as a hypothesis. -/
set_option autoImplicit false
namespace Paper7Schwenk
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

theorem check_SchwenkRecurrenceExactness :
    BackfillPaper7.Challenge.Legacy.Algebra.SchwenkRecurrenceExactness := by
  intro b p q hb u v hu hv
  exact ⟨sunDeleteEdge_chainPolynomial b p q hb u v hu hv,
    endpointDelete_chainPolynomial b p q hb u v hu hv,
    schwenk_cycle_deletion_pq b p q⟩
#print axioms Paper7Schwenk.check_SchwenkRecurrenceExactness

end Paper7Schwenk
