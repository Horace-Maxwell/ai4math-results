import Research.TaskH.Five.EqualityShortCycles
import Research.TaskH.Five.RainbowCycles
import Research.TaskH.Five.LowDegreeComplete
import Research.TaskH.Five.FiveHighDegreeContradiction
import Research.TaskH.Five.Regression

/-! The exact frozen k=5 partial target. The original all-k Question2 is
unchanged and is not asserted by this theorem. -/

set_option autoImplicit false

universe u

namespace TaskH

theorem case_five : Challenge.CaseFive.{u} := by
  intro V _ G hcrit hcount
  classical
  have hc : Challenge.modCycleCount 5 G = 72 :=
    hcount.trans Five.completeSix_check.2.2
  have hs : Five.ShortFiveCycles G := Five.equality_shortFiveCycles hcrit hc
  by_cases hex : ∃ v : V, G.degree v = 5
  · obtain ⟨v, hv⟩ := hex
    exact Five.degreeFive_isCompleteOfOrder hcrit hs hc v hv
  · have hdeg : ∀ v : V, 6 ≤ G.degree v := by
      intro v
      have hd := critical_degree_ge hcrit v
      have hne : G.degree v ≠ 5 := fun he => hex ⟨v, he⟩
      omega
    have hr : Five.RainbowFiveCycles G := Five.equality_rainbowFiveCycles hcrit hc
    exact False.elim (Five.equality_no_high_minDegree hcrit hs hr hc hdeg)

end TaskH

#print axioms TaskH.case_five
#print axioms TaskH.Five.completeSix_check
