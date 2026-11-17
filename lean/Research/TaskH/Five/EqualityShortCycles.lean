import Research.TaskH.Five.Definitions
import Research.TaskH.Five.GoodCycleLowerBound
import Research.TaskH.Five.GoodMultiplicityOrders
import Research.TaskH.FiniteBudget

/-!
The original 120-by-72 actual good-cycle relation is saturated. Its strict
long-cycle multiplier rules out every longer divisible genuine cycle.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Five.GoodCycles

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_good_orders_saturated (hnot : ¬ G.Colorable 5)
    (hcount : modCycleCount 5 G = 72) {v : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 5))
    (s : Finset (Sym2 V)) (hs : s ∈ ModCycleEdgeSets 5 G) :
    (goodCycleOrders c s).card = 10 := by
  classical
  let A : Finset (Equiv.Perm (Fin 5)) := Finset.univ
  let C := (Basics.modCycleEdgeSets_finite 5 G).toFinset
  have hA : A.card = 120 := by norm_num [A, Fintype.card_perm]
  have hC : C.card = 72 := by
    change (Basics.modCycleEdgeSets_finite 5 G).toFinset.card = 72
    rw [← Set.ncard_eq_toFinset_card]
    exact hcount
  have hrow : ∀ π ∈ A, 6 ≤ (C.filter (GoodCycleOrder c π)).card := by
    intro π _
    exact good_mod_cycles_card_ge_six hnot c π
  have hcol : ∀ t ∈ C, (A.filter (fun π => GoodCycleOrder c π t)).card ≤ 10 := by
    intro t _
    exact goodCycleOrders_card_le_ten c t
  have hbalance : A.card * 6 = C.card * 10 := by rw [hA, hC]
  exact FiniteBudget.columns_saturated A C (GoodCycleOrder c) 6 10
    hbalance hrow hcol s ((Basics.modCycleEdgeSets_finite 5 G).mem_toFinset.mpr hs)

theorem equality_shortFiveCycles (hcrit : IsCriticalPlus 5 G)
    (hcount : modCycleCount 5 G = 72) : ShortFiveCycles G := by
  classical
  intro x p hp hd
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit x
  have hs : p.edges.toFinset ∈ ModCycleEdgeSets 5 G :=
    (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr hd
  have he := equality_good_orders_saturated (critical_not_colorable hcrit)
    hcount c p.edges.toFinset hs
  by_contra hlen
  obtain ⟨a, ha⟩ := hd
  have hmin := hp.three_le_length
  have hlong : 10 ≤ p.length := by omega
  have hlt := goodCycleOrders_card_lt_ten_of_long_cycle c p.edges.toFinset
    p hp p.coe_edges_toFinset.symm hlong p.start_mem_support
  omega

end TaskH.Five

#print axioms TaskH.Five.equality_good_orders_saturated
#print axioms TaskH.Five.equality_shortFiveCycles
