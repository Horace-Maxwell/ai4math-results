import Research.TaskH.Six.Definitions
import Research.TaskH.Six.GoodCycleLowerBound
import Research.TaskH.Six.GoodMultiplicityOrders
import Research.TaskH.FiniteBudget

/-!
The original 720-by-420 actual good-cycle relation is saturated. Its strict
long-cycle multiplier rules out every longer divisible genuine cycle.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Six.GoodCycles

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_good_orders_saturated (hnot : ¬ G.Colorable 6)
    (hcount : modCycleCount 6 G = 420) {v : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 6))
    (s : Finset (Sym2 V)) (hs : s ∈ ModCycleEdgeSets 6 G) :
    (goodCycleOrders c s).card = 12 := by
  classical
  let A : Finset (Equiv.Perm (Fin 6)) := Finset.univ
  let C := (Basics.modCycleEdgeSets_finite 6 G).toFinset
  have hA : A.card = 720 := by norm_num [A, Fintype.card_perm]
  have hC : C.card = 420 := by
    change (Basics.modCycleEdgeSets_finite 6 G).toFinset.card = 420
    rw [← Set.ncard_eq_toFinset_card]
    exact hcount
  have hrow : ∀ π ∈ A, 7 ≤ (C.filter (GoodCycleOrder c π)).card := by
    intro π _
    exact good_mod_cycles_card_ge_seven hnot c π
  have hcol : ∀ t ∈ C, (A.filter (fun π => GoodCycleOrder c π t)).card ≤ 12 := by
    intro t _
    exact goodCycleOrders_card_le_twelve c t
  have hbalance : A.card * 7 = C.card * 12 := by rw [hA, hC]
  exact FiniteBudget.columns_saturated A C (GoodCycleOrder c) 7 12
    hbalance hrow hcol s ((Basics.modCycleEdgeSets_finite 6 G).mem_toFinset.mpr hs)

theorem equality_shortSixCycles (hcrit : IsCriticalPlus 6 G)
    (hcount : modCycleCount 6 G = 420) : ShortSixCycles G := by
  classical
  intro x p hp hd
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit x
  have hs : p.edges.toFinset ∈ ModCycleEdgeSets 6 G :=
    (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr hd
  have he := equality_good_orders_saturated (critical_not_colorable hcrit)
    hcount c p.edges.toFinset hs
  by_contra hlen
  obtain ⟨a, ha⟩ := hd
  have hmin := hp.three_le_length
  have hlong : 12 ≤ p.length := by omega
  have hlt := goodCycleOrders_card_lt_twelve_of_long_cycle c p.edges.toFinset
    p hp p.coe_edges_toFinset.symm hlong p.start_mem_support
  omega

end TaskH.Six

#print axioms TaskH.Six.equality_good_orders_saturated
#print axioms TaskH.Six.equality_shortSixCycles
