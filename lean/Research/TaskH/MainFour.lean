import Research.TaskH.EqualityDegree
import Research.TaskH.LowDegreeComplete
import Research.TaskH.Regression

/-!
The exact frozen k=4 subcase. This theorem is a partial result for Task H:
it does not assert the full Question2 over every k>=4.
-/

set_option autoImplicit false

universe u

namespace TaskH

/-- The original critical graph and original modulo-four cycle count suffice. -/
theorem case_four : Challenge.CaseFour.{u} := by
  intro V _ G hcrit hcount
  classical
  have hc : Challenge.modCycleCount 4 G = 15 :=
    hcount.trans completeFive_check.2.2
  have hs : ShortFourCycles G := equality_shortFourCycles hcrit hc
  obtain ⟨v, hv⟩ := equality_exists_degree_four hcrit hc
  exact degreeFour_isCompleteOfOrder hcrit hs hc v hv

end TaskH

#print axioms TaskH.case_four
#print axioms TaskH.completeFive_check
