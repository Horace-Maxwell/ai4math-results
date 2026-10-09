import Research.Backfill.Paper6.LiteralVennFinite4

/-! Source-only repair candidate; one original declaration per compilation unit. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Paper6LiteralLouWang

open BackfillPaper6.V3
open Paper6InclusionExclusionVenn

theorem univ_patterns4 : (Finset.univ : Finset (Finset (Fin 4))) =
    {(∅ : Finset (Fin 4)), ({0} : Finset (Fin 4)), ({1} : Finset (Fin 4)), ({0, 1} : Finset (Fin 4)), ({2} : Finset (Fin 4)), ({0, 2} : Finset (Fin 4)), ({1, 2} : Finset (Fin 4)), ({0, 1, 2} : Finset (Fin 4)), ({3} : Finset (Fin 4)), ({0, 3} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4)), ({0, 1, 3} : Finset (Fin 4)), ({2, 3} : Finset (Fin 4)), ({0, 2, 3} : Finset (Fin 4)), ({1, 2, 3} : Finset (Fin 4)), ({0, 1, 2, 3} : Finset (Fin 4))} := by decide

#print axioms Paper6LiteralLouWang.univ_patterns4

end Paper6LiteralLouWang
