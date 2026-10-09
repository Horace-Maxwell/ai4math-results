import Research.Backfill.Paper6.RemarkPositive
import Research.Backfill.Paper6.PropEExclusion

/-!
# Exact frozen retained remark after Proposition E

This complete composition source may only be compiled once its genuine
dependencies exist and are scheduled by Root:

* RemarkPositive is emitted only after a real five-term weight-362 candidate
  has been found.  Remark362 must then prove its actual RowData5 certificate.
* PropEExclusion supplies the entire necessary interval direction, including
  the low values which are not excluded merely by the statement of PropE.

No missing dependency is replaced by an axiom, placeholder, or added hypothesis.
At author handoff the 362 modules have not been generated, and the exclusion
certificate chain has not been validated.  No completed acceptance is claimed.
-/

set_option autoImplicit false

namespace Paper6RemarkWitnesses

open BackfillPaper6.V3

/-- Exact complete frozen contract; this is the sole new main goal here. -/
theorem check_PropE_remark_2mod4 : BackfillPaper6.V3.PropE_remark_2mod4 := by
  change {w : ℕ | w ∈ weightsLe5 ∧ w % 4 = 2 ∧ 250 ≤ w ∧ w ≤ 400} =
    {w | w = 254 ∨ w = 314 ∨ w = 318 ∨ (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398)}
  apply Set.Subset.antisymm
  · intro w hw
    exact Paper6FiveExclusion.interval_necessary w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
  · exact remark_positive_subset

end Paper6RemarkWitnesses

#print axioms Paper6RemarkWitnesses.check_PropE_remark_2mod4
