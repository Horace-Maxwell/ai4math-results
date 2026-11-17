import Research.TaskH.Five.FiveForbidden
import Research.TaskH.Five.FiveLightEdgeOrder
import Research.TaskH.Five.FiveEqualityWitness
import Research.TaskH.Five.FiveLastBudget
import Research.TaskH.Five.EdgeCyclesCount
import Research.TaskH.Five.SingletonCycles

/-! The high-degree branch uses actual critical-graph cycle witnesses throughout. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge

theorem equality_no_high_minDegree {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hdeg : ∀ v : V, 6 ≤ G.degree v) : False := by
  have hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard :=
    fun {_x _y} hxy => critical_edge_twelve_modCyclesThroughAvoid hcrit hs hxy
  have hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard :=
    critical_singleton_cycle_bound hcrit hs
  have hgem := no_gem_pattern_of_high_minDegree hcrit hs hr hc hdeg hE hsingle
  obtain ⟨f, hf⟩ := equality_exists_pentagon hs hc
  obtain ⟨i, hi, horder⟩ := pentagon_exists_edge_order_bound hcrit hs hr
    (seven_le_card_of_minDegree_six hcrit hdeg) hgem f hf
  exact high_minDegree_edge_order_contradiction hcrit hs hr hc hdeg hE hsingle hi horder

end TaskH.Five

#print axioms TaskH.Five.equality_no_high_minDegree
