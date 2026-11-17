import Research.TaskH.Seven.Definitions
import Research.TaskH.Seven.GoodCycleLowerBound
import Research.TaskH.Seven.GoodMultiplicityOrders
import Research.TaskH.FiniteBudget

/-!
The original 5040-by-2880 actual good-cycle relation is saturated. Its strict
long-cycle multiplier rules out every longer divisible genuine cycle.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.Seven.GoodCycles

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_good_orders_saturated (hnot : ¬ G.Colorable 7)
    (hcount : modCycleCount 7 G = 2880) {v : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (s : Finset (Sym2 V)) (hs : s ∈ ModCycleEdgeSets 7 G) :
    (goodCycleOrders c s).card = 14 := by
  classical
  let A : Finset (Equiv.Perm (Fin 7)) := Finset.univ
  let C := (Basics.modCycleEdgeSets_finite 7 G).toFinset
  have hA : A.card = 5040 := by norm_num [A, Fintype.card_perm]
  have hC : C.card = 2880 := by
    change (Basics.modCycleEdgeSets_finite 7 G).toFinset.card = 2880
    rw [← Set.ncard_eq_toFinset_card]
    exact hcount
  have hrow : ∀ π ∈ A, 8 ≤ (C.filter (GoodCycleOrder c π)).card := by
    intro π _
    exact good_mod_cycles_card_ge_eight hnot c π
  have hcol : ∀ t ∈ C, (A.filter (fun π => GoodCycleOrder c π t)).card ≤ 14 := by
    intro t _
    exact goodCycleOrders_card_le_fourteen c t
  have hbalance : A.card * 8 = C.card * 14 := by rw [hA, hC]
  exact FiniteBudget.columns_saturated A C (GoodCycleOrder c) 8 14
    hbalance hrow hcol s ((Basics.modCycleEdgeSets_finite 7 G).mem_toFinset.mpr hs)

theorem equality_shortSevenCycles (hcrit : IsCriticalPlus 7 G)
    (hcount : modCycleCount 7 G = 2880) : ShortSevenCycles G := by
  classical
  intro x p hp hd
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit x
  have hs : p.edges.toFinset ∈ ModCycleEdgeSets 7 G :=
    (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr hd
  have he := equality_good_orders_saturated (critical_not_colorable hcrit)
    hcount c p.edges.toFinset hs
  by_contra hlen
  obtain ⟨a, ha⟩ := hd
  have hmin := hp.three_le_length
  have hlong : 14 ≤ p.length := by omega
  have hlt := goodCycleOrders_card_lt_fourteen_of_long_cycle c p.edges.toFinset
    p hp p.coe_edges_toFinset.symm hlong p.start_mem_support
  omega

end TaskH.Seven

#print axioms TaskH.Seven.equality_good_orders_saturated
#print axioms TaskH.Seven.equality_shortSevenCycles
