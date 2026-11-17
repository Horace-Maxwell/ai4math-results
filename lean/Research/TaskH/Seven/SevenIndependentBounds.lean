import Research.TaskH.Seven.SevenNeighborIncidence

/-! The original external-capacity-four and actual incidence bounds.
The order-nine condition is internal to the noncomplete equality branch;
no abstract neighbor or cycle-count bound is assumed below. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem critical_degree_le_twenty_seven
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V) (hc : modCycleCount 7 G = 2880) (v : V) :
    G.degree v ≤ 27 := by
  have hrev := critical_reverse_neighbor_cycle_budget hcrit hs hr hn hc v
  have hbase := critical_three_hundred_sixty_one_le_cycleDegree hcrit hs v
  omega

theorem critical_three_hundred_eighty_nine_le_cycleDegree
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V) (hc : modCycleCount 7 G = 2880) (v : V) :
    389 ≤ cycleDegree G v := by
  have hd := critical_degree_le_twenty_seven hcrit hs hr hn hc v
  have hbase := critical_three_hundred_sixty_one_le_cycleDegree hcrit hs v
  have hf := critical_forward_neighbor_cycle_budget_sub hcrit hs v
  have hm := Nat.mul_le_mul_right (cycleDegree G v - 360) hd
  omega

theorem critical_card_le_fifty_one
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V) (hc : modCycleCount 7 G = 2880) :
    Fintype.card V ≤ 51 := by
  have he := sum_cycleDegree_eq_20160 hs hc
  have hl : 389 * Fintype.card V ≤ ∑ v : V, cycleDegree G v := by
    calc
      _ = ∑ _v : V, 389 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ =>
        critical_three_hundred_eighty_nine_le_cycleDegree hcrit hs hr hn hc v)
  omega

end TaskH.Seven

#print axioms TaskH.Seven.critical_degree_le_twenty_seven
#print axioms TaskH.Seven.critical_three_hundred_eighty_nine_le_cycleDegree
#print axioms TaskH.Seven.critical_card_le_fifty_one
