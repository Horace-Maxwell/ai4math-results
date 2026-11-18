import Research.TaskH.General.GoodMultiplicityOrders
import Research.TaskH.General.FactorialBalance
import Research.TaskH.General.EdgeCycles
import Research.TaskH.FiniteBudget

/-!
Actual finite good-cycle relation and exact original factorial balance.
The per-order lower bound is an explicit INTERNAL debt on this same graph,
coloring and genuine edgeSet relation, not a new premise of frozen Main.
-/

set_option autoImplicit false

universe u

namespace TaskH.General

open SimpleGraph _root_.TaskH.Challenge _root_.TaskH.General.GoodCycles

variable {k : ℕ} {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- Precise remaining R interface: actual good unoriented cycle edge sets for
every actual deleted-vertex coloring and every full S_k rank order. -/
noncomputable def ActualGoodCycleLowerBound (k : ℕ) (G : SimpleGraph V) : Prop := by
  classical
  exact ∀ (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (π : Equiv.Perm (Fin k)),
    k + 1 ≤ ((Basics.modCycleEdgeSets_finite k G).toFinset.filter
      (GoodCycleOrder c π)).card

open scoped Classical in
/-- Exact incidence sum over the actual finite cycle-edgeSet collection. -/
theorem actual_good_relation_double_count {v : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) :
    (∑ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))),
      ((Basics.modCycleEdgeSets_finite k G).toFinset.filter
        (GoodCycleOrder c π)).card) =
    ∑ s ∈ (Basics.modCycleEdgeSets_finite k G).toFinset,
      (goodCycleOrders c s).card := by
  classical
  simpa only [goodCycleOrders] using
    (FiniteBudget.relation_double_count
      (Finset.univ : Finset (Equiv.Perm (Fin k)))
      (Basics.modCycleEdgeSets_finite k G).toFinset (GoodCycleOrder c))

/-- Original equality forces every actual column to saturate, conditional
only on the explicitly named actual per-order lower-bound debt. -/
theorem equality_good_orders_saturated (hk : 3 ≤ k)
    (hR : ActualGoodCycleLowerBound k G)
    (hcount : modCycleCount k G = bound k) {v : V}
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (s : Finset (Sym2 V)) (hs : s ∈ ModCycleEdgeSets k G) :
    (goodCycleOrders c s).card = 2 * k := by
  classical
  let A : Finset (Equiv.Perm (Fin k)) := Finset.univ
  let C := (Basics.modCycleEdgeSets_finite k G).toFinset
  have hA : A.card = k.factorial := by simp [A, Fintype.card_perm]
  have hC : C.card = bound k := by
    change (Basics.modCycleEdgeSets_finite k G).toFinset.card = bound k
    rw [← Set.ncard_eq_toFinset_card]
    exact hcount
  have hrow : ∀ π ∈ A, k + 1 ≤ (C.filter (GoodCycleOrder c π)).card := by
    intro π _
    exact hR v c π
  have hcol : ∀ t ∈ C, (A.filter (fun π => GoodCycleOrder c π t)).card ≤ 2 * k := by
    intro t _
    exact goodCycleOrders_card_le_two_mul hk c t
  have hbalance : A.card * (k + 1) = C.card * (2 * k) := by
    rw [hA, hC]
    exact original_bound_balance hk
  exact FiniteBudget.columns_saturated A C (GoodCycleOrder c) (k + 1) (2 * k)
    hbalance hrow hcol s ((Basics.modCycleEdgeSets_finite k G).mem_toFinset.mpr hs)

/-- Conditional S assembly from the original criticality and count. R is
still explicitly owed; no frozen theorem is strengthened to assume it. -/
theorem equality_shortCycles_of_actual_lower_bound (hk : 3 ≤ k)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k)
    (hR : ActualGoodCycleLowerBound k G) : ShortCycles k G := by
  classical
  intro x p hp hd
  obtain ⟨c⟩ := critical_colorable_deletedVertex hcrit x
  have hs : p.edges.toFinset ∈ ModCycleEdgeSets k G :=
    (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr hd
  have he := equality_good_orders_saturated hk hR hcount c p.edges.toFinset hs
  by_contra hlen
  obtain ⟨a, ha⟩ := hd
  have hmin := hp.three_le_length
  have ha1 : 1 ≤ a := by
    by_contra hn
    have hz : a = 0 := by omega
    rw [hz, Nat.mul_zero] at ha
    omega
  have hane : a ≠ 1 := by
    intro h1
    apply hlen
    simpa only [h1, Nat.mul_one] using ha
  have ha2 : 2 ≤ a := by omega
  have hlt := goodCycleOrders_card_lt_two_mul_of_long_divisible_cycle hk c
    p.edges.toFinset p hp p.coe_edges_toFinset.symm a ha2 ha p.start_mem_support
  omega

end TaskH.General

#print axioms TaskH.General.ActualGoodCycleLowerBound
#print axioms TaskH.General.actual_good_relation_double_count
#print axioms TaskH.General.equality_good_orders_saturated
#print axioms TaskH.General.equality_shortCycles_of_actual_lower_bound
