import Research.Backfill.Paper3.Proof.Num.Remark10b
import Research.Backfill.Paper3.Proof.Num.Remark12
import Research.Backfill.Paper3.Proof.Num.TDNum

/-!
# Exact numerics

The statements `Remark10b`, `Remark12` and `TheoremDNumerics` of
`Research.Backfill.Paper3.Challenge`, proved with no hypotheses: every count is a prefix sum of
coefficients of `P_d^m` or `P_{H_d}^{⌊m/2⌋} P_d^{m mod 2}` (`Research.Backfill.Paper3.Proof.Num.Bridge`), computed by a
verified list-polynomial loop (`Research.Backfill.Paper3.Proof.Num.ListPoly`, `Research.Backfill.Paper3.Proof.Num.Loop`) that the kernel evaluates
(`Research.Backfill.Paper3.Proof.Num.Run*`).
-/

set_option autoImplicit false

namespace P3Num

open BackfillPaper3.Challenge

theorem check_Remark10b : Remark10b := remark10b

#print axioms check_Remark10b

theorem check_Remark12 : Remark12 := remark12

#print axioms check_Remark12

theorem check_TheoremDNumerics : TheoremDNumerics := theoremDNumerics

#print axioms check_TheoremDNumerics

end P3Num
