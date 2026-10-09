import Research.Backfill.Paper6.LiteralVennFinite3

/-! Source-only repair candidate; one original declaration per compilation unit. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

theorem univ_patterns3 : (Finset.univ : Finset (Finset (Fin 3))) =
    {(∅ : Finset (Fin 3)), ({0} : Finset (Fin 3)), ({1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({2} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3)), ({0, 1, 2} : Finset (Fin 3))} := by decide

#print axioms Paper6LiteralLouWang.univ_patterns3

end Paper6LiteralLouWang
