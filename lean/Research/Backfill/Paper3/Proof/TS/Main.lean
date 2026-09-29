import Research.Backfill.Paper3.Proof.TS.Connected
import Research.Backfill.Paper3.Proof.TS.Table2

/-!
# The 2-switch theorem and Table 2

`check_TwoSwitchConnected`: the 2-switch theorem (`Research.Backfill.Paper3.Proof.TS.Connected`).
`check_Table2`: Table 2 (`Research.Backfill.Paper3.Proof.TS.Table2`, data modules `Research.Backfill.Paper3.Proof.TS.D3`, `Research.Backfill.Paper3.Proof.TS.D4`, `Research.Backfill.Paper3.Proof.TS.D5*`).
-/

set_option autoImplicit false

namespace P3TS

theorem check_TwoSwitchConnected : BackfillPaper3.Challenge.TwoSwitchConnected :=
  twoSwitchConnected

#print axioms check_TwoSwitchConnected

theorem check_Table2 : BackfillPaper3.Challenge.Table2 :=
  table2

#print axioms check_Table2

end P3TS
