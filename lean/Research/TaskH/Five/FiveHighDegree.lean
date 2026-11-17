import Research.TaskH.Five.FiveNeighborIncidence
import Research.TaskH.Five.FiveAttachment

/-!
The shortened high-degree counting prefix. All quantities are the original
graph degrees and the original modulo-five edge-set incidence counts.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem critical_has_vertex (hcrit : IsCriticalPlus 5 G) : Nonempty V := by
  classical
  by_contra hn
  apply TaskH.critical_not_colorable hcrit
  refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 5)) ?_⟩
  intro a b _
  exact False.elim (hn ⟨a⟩)

variable [Fintype V] [DecidableRel G.Adj]

theorem seven_le_card_of_minDegree_six (hcrit : IsCriticalPlus 5 G)
    (hdeg : ∀ v : V, 6 ≤ G.degree v) : 7 ≤ Fintype.card V := by
  obtain ⟨v⟩ := critical_has_vertex hcrit
  have hl := hdeg v
  have hu := G.degree_lt_card_verts v
  omega

theorem high_degree_eight_or_nine
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard) (v : V) :
    G.degree v = 8 ∨ G.degree v = 9 := by
  have hn := seven_le_card_of_minDegree_six hcrit hdeg
  have hlo := hdeg v
  have h13 := thirteen_le_cycleDegree hcrit hE v
  have hsinglev := hsingle v
  rw [← cycleDegree_eq_ncard] at hsinglev
  have hu := cycleDegree_add_six_degree_le_seventy_two hc hE
    (outside_cycle_neighbors_card_le_two hcrit hs hr hn) v
  omega

theorem cycleDegree_eq_twenty_four_of_degree_eight
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    {v : V} (hd : G.degree v = 8) : cycleDegree G v = 24 := by
  have hn := seven_le_card_of_minDegree_six hcrit hdeg
  have hl := hsingle v
  rw [← cycleDegree_eq_ncard, hd] at hl
  have hu := cycleDegree_add_six_degree_le_seventy_two hc hE
    (outside_cycle_neighbors_card_le_two hcrit hs hr hn) v
  rw [hd] at hu
  omega

theorem sixteen_le_cycleDegree_of_high_minDegree
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard) (v : V) :
    16 ≤ cycleDegree G v := by
  rcases high_degree_eight_or_nine hcrit hs hr hc hdeg hE hsingle v with hd | hd
  · have he := cycleDegree_eq_twenty_four_of_degree_eight hcrit hs hr hc hdeg hE hsingle hd
    omega
  · have hb := forward_neighbor_cycle_budget hs hE v
    rw [hd] at hb
    omega

theorem card_le_twenty_two_of_high_minDegree
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard) :
    Fintype.card V ≤ 22 := by
  have hsum := sum_cycleDegree_eq_360 hs hc
  have hl : 16 * Fintype.card V ≤ ∑ v : V, cycleDegree G v := by
    calc
      _ = ∑ _v : V, 16 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v _ =>
        sixteen_le_cycleDegree_of_high_minDegree hcrit hs hr hc hdeg hE hsingle v)
  omega

theorem nine_le_card_of_high_minDegree
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard) :
    9 ≤ Fintype.card V := by
  obtain ⟨v⟩ := critical_has_vertex hcrit
  have hd := high_degree_eight_or_nine hcrit hs hr hc hdeg hE hsingle v
  have hu := G.degree_lt_card_verts v
  omega

end TaskH.Five

#print axioms TaskH.Five.critical_has_vertex
#print axioms TaskH.Five.seven_le_card_of_minDegree_six
#print axioms TaskH.Five.high_degree_eight_or_nine
#print axioms TaskH.Five.cycleDegree_eq_twenty_four_of_degree_eight
#print axioms TaskH.Five.sixteen_le_cycleDegree_of_high_minDegree
#print axioms TaskH.Five.card_le_twenty_two_of_high_minDegree
#print axioms TaskH.Five.nine_le_card_of_high_minDegree
