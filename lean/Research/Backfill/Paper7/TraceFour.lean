import Research.Backfill.Paper7.FourWalkTuples
import Research.Backfill.Paper7.TraceWalkCounts

/-! Fourth trace for an arbitrary finite graph, with the genuine based-cycle
cardinality left explicit for the independently authored 2g fibre bridge. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph Finset
open scoped Classical

namespace Paper7FourWalks

variable {V : Type} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

theorem trace_four_eq_quad_card :
    ((H.adjMatrix ℤ) ^ 4).trace = (Fintype.card (Quad H) : ℤ) := by
  rw [Paper7Moments.trace_eq_closed_walk_count]
  have hc := Fintype.card_congr (quadClosedEquiv H)
  rw [Fintype.card_sigma] at hc
  exact_mod_cast hc.symm

theorem trace_four_with_based_cycles :
    ((H.adjMatrix ℤ) ^ 4).trace = 2 * (H.edgeFinset.card : ℤ) +
      2 * ∑ v, (H.degree v : ℤ) * ((H.degree v : ℤ) - 1) +
        (Nat.card {p : Σ u : V, H.Walk u u // p.2.IsCycle ∧ p.2.length = 4} : ℤ) := by
  have hclass : (Fintype.card (Quad H) : ℤ) + 2 * (H.edgeFinset.card : ℤ) =
      2 * (∑ v : V, (H.degree v : ℤ) ^ 2) +
        (Nat.card {p : Σ u : V, H.Walk u u // p.2.IsCycle ∧ p.2.length = 4} : ℤ) := by
    exact_mod_cast quad_card_classification H
  have hdegrees : (∑ v : V, (H.degree v : ℤ)) = 2 * (H.edgeFinset.card : ℤ) := by
    exact_mod_cast H.sum_degrees_eq_twice_card_edges
  have htheta : (∑ v : V, (H.degree v : ℤ) * ((H.degree v : ℤ) - 1)) =
      (∑ v : V, (H.degree v : ℤ) ^ 2) - ∑ v : V, (H.degree v : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [trace_four_eq_quad_card]
  linarith only [hclass, hdegrees, htheta]

end Paper7FourWalks

#print axioms Paper7FourWalks.trace_four_eq_quad_card
#print axioms Paper7FourWalks.trace_four_with_based_cycles
