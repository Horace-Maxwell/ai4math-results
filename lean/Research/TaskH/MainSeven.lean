import Research.TaskH.Seven.SevenMinimumThirteen
import Research.TaskH.Seven.SevenFinalBridge
import Research.TaskH.Seven.SevenOriginalLowerBound
import Research.TaskH.Seven.SevenCompleteCheck

/-! Exact frozen k=7 partial target, on every finite vertex type and with
proper-subgraph criticality and genuine unoriented cycle edge-set counts.
The original all-k question is unchanged and remains a separate target. -/

set_option autoImplicit false

universe u

namespace TaskH

theorem case_seven : Challenge.CaseSeven.{u} := by
  intro V _ G hcrit hcount
  classical
  have hc : Challenge.modCycleCount 7 G = 2880 :=
    hcount.trans Seven.bound_seven_eq_2880
  by_contra hnot
  exact hnot (Seven.equality_complete_of_min_degree_thirteen hcrit hc
    (Seven.equality_noncomplete_degree_ge_thirteen hcrit hc hnot))

end TaskH

#print axioms TaskH.case_seven
#print axioms TaskH.lower_bound_seven
#print axioms TaskH.Seven.completeEight_check
