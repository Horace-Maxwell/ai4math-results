import Research.Backfill.Paper7.ChallengeV2
import Research.Backfill.Paper7.CycleFirstDart

set_option autoImplicit false

noncomputable section

open SimpleGraph Finset
open scoped Classical
open BackfillPaper7.Challenge

namespace Paper7Cycles

variable {V : Type} [Fintype V] [DecidableEq V]

abbrev BasedCycle (H : SimpleGraph V) [DecidableRel H.Adj] (g : ℕ) :=
  Σ u : V, {w : {w : H.Walk u u // w.length = g} // w.val.IsCycle}

#print axioms Paper7Cycles.BasedCycle

def basedCycleEdges {H : SimpleGraph V} [DecidableRel H.Adj] {g : ℕ}
    (w : BasedCycle H g) : Finset (Sym2 V) := w.2.val.val.edges.toFinset

#print axioms Paper7Cycles.basedCycleEdges

def basedCycleFirstDart {H : SimpleGraph V} [DecidableRel H.Adj] {g : ℕ}
    (w : BasedCycle H g) : H.Dart := w.2.val.val.firstDart w.2.property.not_nil

#print axioms Paper7Cycles.basedCycleFirstDart

omit [Fintype V] in
theorem basedCycleEdges_mem {H : SimpleGraph V} [DecidableRel H.Adj] {g : ℕ}
    (w : BasedCycle H g) : basedCycleEdges w ∈ cycleEdgeSets H g :=
  ⟨w.1, w.2.val.val, w.2.property, w.2.val.property, rfl⟩

#print axioms Paper7Cycles.basedCycleEdges_mem

omit [Fintype V] in
theorem firstDart_mem_basedCycleEdges {H : SimpleGraph V} [DecidableRel H.Adj] {g : ℕ}
    (w : BasedCycle H g) : (basedCycleFirstDart w).edge ∈ basedCycleEdges w := by
  apply List.mem_toFinset.mpr
  exact Walk.adj_toSubgraph_iff_mem_edges.mp
    (w.2.val.val.toSubgraph_adj_snd w.2.property.not_nil)

#print axioms Paper7Cycles.firstDart_mem_basedCycleEdges

end Paper7Cycles
