import Research.TaskH.GoodCycleLowerBound
import Research.TaskH.GoodMultiplicityOrders
import Research.TaskH.FiniteBudget
import Research.TaskH.EdgeCycles

/-!
Equality in the actual good-cycle double count rules out all longer divisible
cycles. The row and column bounds are proved for the original graph, not
introduced as hypotheses of the frozen equality-case statement.
-/

set_option autoImplicit false

universe u

namespace TaskH

open SimpleGraph Challenge GoodCycles

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem equality_good_orders_saturated (hnot : ¬ G.Colorable 4)
    (hcount : modCycleCount 4 G = 15) {v : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 4))
    (s : Finset (Sym2 V)) (hs : s ∈ ModCycleEdgeSets 4 G) :
    (goodCycleOrders c s).card = 8 := by
  classical
  let A : Finset (Equiv.Perm (Fin 4)) := Finset.univ
  let C := (Basics.modCycleEdgeSets_finite 4 G).toFinset
  have hA : A.card = 24 := by norm_num [A, Fintype.card_perm]
  have hC : C.card = 15 := by
    change (Basics.modCycleEdgeSets_finite 4 G).toFinset.card = 15
    rw [← Set.ncard_eq_toFinset_card]
    exact hcount
  have hrow : ∀ π ∈ A, 5 ≤ (C.filter (GoodCycleOrder c π)).card := by
    intro π _
    exact good_mod_cycles_card_ge_five hnot c π
  have hcol : ∀ t ∈ C, (A.filter (fun π => GoodCycleOrder c π t)).card ≤ 8 := by
    intro t _
    exact goodCycleOrders_card_le_eight c t
  have hsat := FiniteBudget.twenty_four_fifteen_columns_eq_eight
    A C (GoodCycleOrder c) hA hC hrow hcol s
      ((Basics.modCycleEdgeSets_finite 4 G).mem_toFinset.mpr hs)
  exact hsat

/-- S: no divisible cycle of length at least eight survives equality. -/
theorem equality_shortFourCycles (hcrit : IsCriticalPlus 4 G)
    (hcount : modCycleCount 4 G = 15) : ShortFourCycles G := by
  classical
  intro x p hp hd
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit x
  have hs : p.edges.toFinset ∈ ModCycleEdgeSets 4 G :=
    (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr hd
  have he := equality_good_orders_saturated (critical_not_colorable hcrit)
    hcount c p.edges.toFinset hs
  by_contra hlen
  obtain ⟨a, ha⟩ := hd
  have hmin := hp.three_le_length
  have hlong : 8 ≤ p.length := by omega
  have hlt := goodCycleOrders_card_lt_eight_of_long_cycle c p.edges.toFinset
    p hp p.coe_edges_toFinset.symm hlong p.start_mem_support
  omega

end TaskH

#print axioms TaskH.equality_good_orders_saturated
#print axioms TaskH.equality_shortFourCycles
