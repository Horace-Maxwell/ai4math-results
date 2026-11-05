import Research.Backfill.Paper7.CycleDartFibres

set_option autoImplicit false

noncomputable section

open SimpleGraph Finset
open scoped Classical
open BackfillPaper7.Challenge

namespace Paper7Cycles

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Every finite simple graph, including the empty graph, has exactly 2g based
oriented representations per undirected length-g simple-cycle edge set. -/
theorem basedCycle_card (H : SimpleGraph V) [DecidableRel H.Adj] (g : ℕ) :
    Fintype.card (BasedCycle H g) = 2 * g * cycleCount H g := by
  let S : Finset (Finset (Sym2 V)) := (cycleEdgeSets H g).toFinset
  have hScard : S.card = cycleCount H g :=
    (Set.ncard_eq_toFinset_card' (cycleEdgeSets H g)).symm
  have hm : (↑(Finset.univ : Finset (BasedCycle H g)) : Set (BasedCycle H g)).MapsTo
      basedCycleEdges (S : Set (Finset (Sym2 V))) := by
    intro w _
    exact Set.mem_toFinset.mpr (basedCycleEdges_mem w)
  calc
    Fintype.card (BasedCycle H g) = (Finset.univ : Finset (BasedCycle H g)).card := by simp
    _ = ∑ s ∈ S, (Finset.univ.filter (fun w : BasedCycle H g => basedCycleEdges w = s)).card :=
      Finset.card_eq_sum_card_fiberwise hm
    _ = ∑ _s ∈ S, 2 * g := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Fintype.card_subtype]
      exact cycleFibre_card s (Set.mem_toFinset.mp hs)
    _ = 2 * g * cycleCount H g := by simp [hScard, Nat.mul_comm]

#print axioms Paper7Cycles.basedCycle_card

end Paper7Cycles
