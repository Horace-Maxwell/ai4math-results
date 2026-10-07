import Research.Backfill.Paper5.Proof.DiagramUnits

set_option autoImplicit false

namespace CodexPaper5.DiagramModel

open BackfillPaper5

/-- All quantifiers of the frozen ModelMonoid target, using the actual list-search product. -/
theorem check_ModelMonoid : Challenge.ModelMonoid := by
  intro n
  refine ⟨?_, ?_, DiagramUnits.idD_mem_B n, ?_⟩
  · intro x hx y hy
    exact DiagramProduct.dmul_isPB hx hy
  · intro x hx y hy
    exact DiagramProduct.dmul_mem_B hx hy
  · intro x hx
    exact ⟨DiagramUnits.dmul_id_left x hx, DiagramUnits.dmul_id_right x hx⟩

#print axioms CodexPaper5.DiagramModel.check_ModelMonoid

end CodexPaper5.DiagramModel
