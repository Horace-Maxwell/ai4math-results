import Research.Backfill.Paper6.CheckThmA
import Research.Backfill.Paper6.FiniteFacts
import Research.Backfill.Paper6.ConcatIdentity
import Research.Backfill.Paper6.S0Comparison

/-! Five exact frozen V3 contracts. ThmA_mathlib is an equivalent restatement
in CheckThmA and earns no additional mathematical credit. -/
set_option autoImplicit false
namespace Paper6FirstBatch

theorem check_ThmA : BackfillPaper6.V3.ThmA := Paper6ThmA.thmA

theorem check_S0_card : BackfillPaper6.V3.S0_card := Paper6FiniteFacts.check_S0_card

theorem check_IntroMU : BackfillPaper6.V3.IntroMU := Paper6FiniteFacts.check_IntroMU

theorem check_Sec4Concat : BackfillPaper6.V3.Sec4Concat := Paper6Concat.check_Sec4Concat

theorem check_S0_eq_LA : BackfillPaper6.V3.S0_eq_LA := Paper6FiniteFacts.check_S0_eq_LA

end Paper6FirstBatch
#print axioms Paper6FirstBatch.check_ThmA
#print axioms Paper6FirstBatch.check_S0_card
#print axioms Paper6FirstBatch.check_IntroMU
#print axioms Paper6FirstBatch.check_Sec4Concat
#print axioms Paper6FirstBatch.check_S0_eq_LA
#print Paper6FirstBatch.check_ThmA
#print Paper6FirstBatch.check_S0_card
#print Paper6FirstBatch.check_IntroMU
#print Paper6FirstBatch.check_Sec4Concat
#print Paper6FirstBatch.check_S0_eq_LA
