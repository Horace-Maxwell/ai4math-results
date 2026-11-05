import Research.Backfill.Paper7.IntroDegreeThreshold
import Research.Backfill.Paper7.IntroDeletedVertexGap

/-! Exact original degrees, retaining the one possible edge lost at a vertex deletion. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroHighVertex
open SimpleGraph BackfillPaper7.Challenge Paper7IntroCutGap Paper7IntroHighBranch

theorem vertex_deleted_degree_restore
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (i : {w : V // w ≠ v}) :
    G.degree i.val = (vertexDeletedGraph G v).degree i +
      if G.Adj i.val v then 1 else 0 := by
  have hdegree : (vertexDeletedGraph G v).degree i =
      ((G.neighborFinset i.val).erase v).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_map (Function.Embedding.subtype (fun w : V => w ≠ v))]
    congr 1
    ext w
    simp [vertexDeletedGraph, SimpleGraph.mem_neighborFinset, Finset.mem_erase, and_comm]
    constructor
    · rintro ⟨hw, hadj⟩
      exact ⟨hw, ((vertexDeletedGraph G v).mem_neighborFinset i ⟨w, hw⟩).mp hadj⟩
    · rintro ⟨hw, hadj⟩
      exact ⟨hw, ((vertexDeletedGraph G v).mem_neighborFinset i ⟨w, hw⟩).mpr hadj⟩
  rw [hdegree]
  by_cases hadj : G.Adj i.val v
  · rw [ite_eq_left hadj]
    exact (Finset.card_erase_add_one ((G.mem_neighborFinset i.val v).mpr hadj)).symm
  · have hnot : v ∉ G.neighborFinset i.val := fun h =>
      hadj ((G.mem_neighborFinset i.val v).mp h)
    rw [ite_eq_right hadj, Finset.erase_eq_of_notMem hnot, add_zero]
    rfl
#print axioms Paper7IntroHighVertex.vertex_deleted_degree_restore

theorem deleted_component_original_degree_restore
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent) (i : C.supp) :
    G.degree i.val.val = ((vertexDeletedGraph G v).induce C.supp).degree i +
      if G.Adj i.val.val v then 1 else 0 := by
  rw [component_degree_eq]
  exact vertex_deleted_degree_restore G v i.val
#print axioms Paper7IntroHighVertex.deleted_component_original_degree_restore

theorem deleted_complement_original_degree_restore
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (C : (vertexDeletedGraph G v).ConnectedComponent) (i : {u : {w : V // w ≠ v} // u ∉ C.supp}) :
    G.degree i.val.val = ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).degree i +
      if G.Adj i.val.val v then 1 else 0 := by
  have hdegree : ((vertexDeletedGraph G v).induce (C.suppᶜ : Set {w : V // w ≠ v})).degree i =
      (vertexDeletedGraph G v).degree i.val := by
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro j hj
    show j ∉ C.supp
    intro hjC
    have hadj : (vertexDeletedGraph G v).Adj i.val j := hj
    exact i.property (C.mem_supp_of_adj_mem_supp hjC hadj.symm)
  rw [hdegree]
  exact vertex_deleted_degree_restore G v i.val
#print axioms Paper7IntroHighVertex.deleted_complement_original_degree_restore

end Paper7IntroHighVertex
