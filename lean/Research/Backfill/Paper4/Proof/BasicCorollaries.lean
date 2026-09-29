import Research.Backfill.Paper4.Proof.Readings
import Research.HKOTriameterDH

/-! Two complete frozen targets, using the accepted reading equivalence and
the released concrete four-point certificates. No distance-heredity conclusion
is substituted for the four-point condition. Acceptance is recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4
open BackfillPaper4

theorem check_Remark5_i : Challenge.Remark5_i := by
  intro V _ G hc hT
  have h4 : Challenge.Question4 G := by
    intro x y hxy
    exact ⟨x, Readings.triametral_of_two G hc hT hxy x⟩
  refine ⟨h4, ?_⟩
  intro hcard
  exact (check_Sec2_readings_Q4 V G hc hcard).1.mp h4

/-- Each reused graph, metric and four-point predicate agrees definitionally
with its frozen counterpart; Lean checks those conversions at these five uses. -/
theorem check_Released_fourPoint_facts : Challenge.Released_fourPoint_facts :=
  ⟨HKOTriameter.F1G_fourPoint, HKOTriameter.F1H_fourPoint,
    HKOTriameter.G2_fourPoint, HKOTriameter.G1_not_fourPoint,
    HKOTriameter.F1G_not_median⟩

#print axioms check_Remark5_i
#print axioms check_Released_fourPoint_facts
end CodexPaper4
