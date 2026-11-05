import Research.Backfill.Paper7.ChallengeV2
import Research.Backfill.Paper7.OddWalkExtraction

set_option autoImplicit false

namespace Paper7OddWalk

open SimpleGraph BackfillPaper7.Challenge

/-- A Mathlib cycle supplies exactly the edge-set representative used by the
frozen definition of `cycleEdgeSets`. -/
theorem cycle_edges_mem_cycleEdgeSets {V : Type} [DecidableEq V]
    {H : SimpleGraph V} {u : V} (c : H.Walk u u) (hc : c.IsCycle) :
    c.edges.toFinset ∈ cycleEdgeSets H c.length :=
  ⟨u, c, hc, rfl, rfl⟩

#print axioms Paper7OddWalk.cycle_edges_mem_cycleEdgeSets

/-- The extracted odd cycle has a representative in the original frozen
edge-set cycle space, and its edges come from the supplied closed walk. -/
theorem exists_cycleEdgeSet_of_odd_closedWalk {V : Type} [DecidableEq V]
    {H : SimpleGraph V} {u : V} (w : H.Walk u u) (hodd : Odd w.length) :
    ∃ (L : ℕ) (s : Finset (Sym2 V)),
      Odd L ∧ L ≤ w.length ∧ s ∈ cycleEdgeSets H L ∧ s ⊆ w.edges.toFinset := by
  obtain ⟨_v, c, hc, hcodd, hcle, hcedges⟩ := exists_odd_cycle_length_le w hodd
  refine ⟨c.length, c.edges.toFinset, hcodd, hcle,
    cycle_edges_mem_cycleEdgeSets c hc, ?_⟩
  intro e he
  exact List.mem_toFinset.mpr (hcedges (List.mem_toFinset.mp he))

#print axioms Paper7OddWalk.exists_cycleEdgeSet_of_odd_closedWalk

/-- Frozen odd girth is a lower bound for every odd closed walk, without any
assumption that the walk itself is a trail or a cycle. -/
theorem oddGirth_le_closedWalk_length {V : Type} [DecidableEq V]
    {H : SimpleGraph V} {g : ℕ} (hg : IsOddGirth H g) {u : V}
    (w : H.Walk u u) (hodd : Odd w.length) : g ≤ w.length := by
  obtain ⟨v, c, hc, hcodd, hcle, _hcedges⟩ := exists_odd_cycle_length_le w hodd
  exact (hg.2.2 v c hc hcodd).trans hcle

#print axioms Paper7OddWalk.oddGirth_le_closedWalk_length

/-- There are no odd closed walks shorter than the frozen odd girth. -/
theorem no_odd_closedWalk_of_length_lt_oddGirth {V : Type} [DecidableEq V]
    {H : SimpleGraph V} {g : ℕ} (hg : IsOddGirth H g) {u : V} {L : ℕ}
    (w : H.Walk u u) (hlen : w.length = L) (hL : Odd L) (hlt : L < g) : False := by
  have hodd : Odd w.length := hlen.symm ▸ hL
  have hle := oddGirth_le_closedWalk_length hg w hodd
  omega

#print axioms Paper7OddWalk.no_odd_closedWalk_of_length_lt_oddGirth

/-- A closed walk whose length is the frozen odd girth must itself be a cycle. -/
theorem isCycle_of_length_eq_oddGirth {V : Type} [DecidableEq V]
    {H : SimpleGraph V} {g : ℕ} (hg : IsOddGirth H g) {u : V}
    (w : H.Walk u u) (hlen : w.length = g) : w.IsCycle := by
  classical
  by_contra hnot
  have hodd : Odd w.length := hlen.symm ▸ hg.1
  obtain ⟨_v, q, hqodd, hqlt, _hqedges⟩ := exists_shorter_odd_closedWalk w hodd hnot
  have hle := oddGirth_le_closedWalk_length hg q hqodd
  omega

#print axioms Paper7OddWalk.isCycle_of_length_eq_oddGirth

/-- Every closed walk of odd-girth length represents a frozen cycle edge set. -/
theorem closedWalk_edges_mem_cycleEdgeSets_of_length_eq_oddGirth
    {V : Type} [DecidableEq V] {H : SimpleGraph V} {g : ℕ}
    (hg : IsOddGirth H g) {u : V} (w : H.Walk u u) (hlen : w.length = g) :
    w.edges.toFinset ∈ cycleEdgeSets H g :=
  ⟨u, w, isCycle_of_length_eq_oddGirth hg w hlen, hlen, rfl⟩

#print axioms Paper7OddWalk.closedWalk_edges_mem_cycleEdgeSets_of_length_eq_oddGirth

/-- The existence clause in the frozen odd-girth predicate gives a positive
frozen cycle count when the graph vertex type is finite. -/
theorem cycleCount_oddGirth_pos {V : Type} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {g : ℕ} (hg : IsOddGirth H g) : 0 < cycleCount H g := by
  obtain ⟨u, c, hc, hlen⟩ := hg.2.1
  change 0 < (cycleEdgeSets H g).ncard
  apply (Set.ncard_pos (Set.toFinite _)).mpr
  exact ⟨c.edges.toFinset, u, c, hc, hlen, rfl⟩

#print axioms Paper7OddWalk.cycleCount_oddGirth_pos

end Paper7OddWalk
