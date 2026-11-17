import Research.TaskH.Five.FiveHighDegree

/-! The last incidence contradiction uses actual vertex and cycle degrees.
The edge-order lower bound is supplied by the separate critical coloring
argument, rather than added to the original equality statement. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem high_minDegree_edge_order_contradiction
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    {u v : V} (huv : G.Adj u v)
    (horder : G.degree u + G.degree v + 6 ≤ Fintype.card V) : False := by
  have hu := high_degree_eight_or_nine hcrit hs hr hc hdeg hE hsingle u
  have hv := high_degree_eight_or_nine hcrit hs hr hc hdeg hE hsingle v
  have hn := card_le_twenty_two_of_high_minDegree hcrit hs hr hc hdeg hE hsingle
  have hdu : G.degree u = 8 := by omega
  have hdv : G.degree v = 8 := by omega
  have hn22 : Fintype.card V = 22 := by omega
  have hcu := cycleDegree_eq_twenty_four_of_degree_eight hcrit hs hr hc hdeg hE hsingle hdu
  have hcv := cycleDegree_eq_twenty_four_of_degree_eight hcrit hs hr hc hdeg hE hsingle hdv
  have hrow : ∀ x : V,
      16 + (if x = u then 8 else 0) + (if x = v then 8 else 0) ≤ cycleDegree G x := by
    intro x
    by_cases hxu : x = u
    · have hxv : x ≠ v := fun he => huv.ne (hxu.symm.trans he)
      simp only [ite_eq_left hxu, ite_eq_right hxv]
      rw [hxu]
      omega
    · by_cases hxv : x = v
      · simp only [ite_eq_right hxu, ite_eq_left hxv]
        rw [hxv]
        omega
      · simp only [ite_eq_right hxu, ite_eq_right hxv, Nat.add_zero]
        exact sixteen_le_cycleDegree_of_high_minDegree hcrit hs hr hc hdeg hE hsingle x
  have htotal := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun x _ => hrow x)
  have h16 : (∑ _x : V, 16) = 16 * Fintype.card V := by simp [Nat.mul_comm]
  have h8u : (∑ x : V, if x = u then 8 else 0) = 8 := by simp
  have h8v : (∑ x : V, if x = v then 8 else 0) = 8 := by simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h16, h8u, h8v,
    sum_cycleDegree_eq_360 hs hc, hn22] at htotal
  omega

end TaskH.Five

#print axioms TaskH.Five.high_minDegree_edge_order_contradiction
