import Research.Backfill.Paper6.ThmA

/-! Exact checks against the frozen V3 target and its Mathlib-only restatement.
The restatement is the same mathematical goal and earns no additional goal count. -/

set_option autoImplicit false

namespace Paper6ThmA.Check

theorem check_ThmA : BackfillPaper6.V3.ThmA := Paper6ThmA.thmA

theorem check_ThmA_mathlib : BackfillPaper6.V3.ThmA_mathlib :=
  Paper6ThmA.thmA_mathlib

end Paper6ThmA.Check

#print axioms Paper6ThmA.Check.check_ThmA
#print axioms Paper6ThmA.Check.check_ThmA_mathlib
#print Paper6ThmA.Check.check_ThmA
#print Paper6ThmA.Check.check_ThmA_mathlib
