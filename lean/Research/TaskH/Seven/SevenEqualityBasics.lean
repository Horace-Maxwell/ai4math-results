import Research.TaskH.Seven.RainbowCycles
import Research.TaskH.Seven.SevenIndependentBounds
import Research.TaskH.Seven.SevenLowerBound

/-! The original criticality and modulo-seven equality discharge S/R/E
internally. These wrappers retain the original finite edge-set count. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_sum_cycleDegree
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880) :
    (∑ v : V, cycleDegree G v) = 20160 :=
  sum_cycleDegree_eq_20160 (equality_shortSevenCycles hcrit hc) hc

theorem equality_edge_three_hundred_sixty_modCyclesThroughAvoid
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    {x y : V} (hxy : G.Adj x y) :
    360 ≤ (TaskH.modCyclesThroughAvoid 7 G x y).ncard :=
  critical_edge_three_hundred_sixty_modCyclesThroughAvoid hcrit
    (equality_shortSevenCycles hcrit hc) hxy

theorem equality_three_hundred_sixty_one_le_cycleDegree [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880) (v : V) :
    361 ≤ cycleDegree G v :=
  critical_three_hundred_sixty_one_le_cycleDegree hcrit
    (equality_shortSevenCycles hcrit hc) v

theorem equality_degree_le_twenty_seven [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hn : 9 ≤ Fintype.card V) (v : V) : G.degree v ≤ 27 :=
  critical_degree_le_twenty_seven hcrit (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) hn hc v

theorem equality_three_hundred_eighty_nine_le_cycleDegree [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hn : 9 ≤ Fintype.card V) (v : V) : 389 ≤ cycleDegree G v :=
  critical_three_hundred_eighty_nine_le_cycleDegree hcrit
    (equality_shortSevenCycles hcrit hc) (equality_rainbowSevenCycles hcrit hc) hn hc v

theorem equality_card_le_fifty_one [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hn : 9 ≤ Fintype.card V) : Fintype.card V ≤ 51 :=
  critical_card_le_fifty_one hcrit (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) hn hc

end TaskH.Seven

#print axioms TaskH.Seven.equality_sum_cycleDegree
#print axioms TaskH.Seven.equality_edge_three_hundred_sixty_modCyclesThroughAvoid
#print axioms TaskH.Seven.equality_three_hundred_sixty_one_le_cycleDegree
#print axioms TaskH.Seven.equality_degree_le_twenty_seven
#print axioms TaskH.Seven.equality_three_hundred_eighty_nine_le_cycleDegree
#print axioms TaskH.Seven.equality_card_le_fifty_one
