import Research.Backfill.Paper7.BMSSunPendant

/-! Exact frozen contracts; all local candidate imports still await Root execution. -/
set_option autoImplicit false
namespace Paper7BMS

theorem check_BMSTheorem21General : BackfillPaper7.Challenge.BMSTheorem21General :=
  bms_general
#print axioms Paper7BMS.check_BMSTheorem21General

theorem check_BMSTheorem21 : BackfillPaper7.Challenge.BMSTheorem21 := bms_sun
#print axioms Paper7BMS.check_BMSTheorem21

theorem check_OnlyP1P2 : BackfillPaper7.Challenge.OnlyP1P2 := only_p1_p2
#print axioms Paper7BMS.check_OnlyP1P2

end Paper7BMS
