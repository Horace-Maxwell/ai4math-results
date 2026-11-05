import Research.Backfill.Paper7.UnicyclicCyclePath

/-! Source-only structural progress for arbitrary unicyclic graphs. Removing
the actual unique cycle leaves a forest, including an empty complement.
No branching exclusion, path-component enumeration or Intro check is claimed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicStructure
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7UnicyclicSchwenk

theorem unicyclic_off_cycle_isAcyclic {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b) :
    (deleteVertices G {v | v ∈ w.support}).IsAcyclic := by
  have he : s(r, w.snd) ∈ w.edges := w.mk_start_snd_mem_edges hw.not_nil
  have ht := cycle_edge_deleted_tree G b hG r w hw hlen r w.snd he
  have hf : (deleteVertices (G.deleteEdges ({s(r, w.snd)} : Set (Sym2 V)))
      {v | v ∈ w.support}).IsAcyclic :=
    ht.isAcyclic.induce {v | v ∉ w.support}
  rw [deleteVertices_deleteEdge G r w.snd {v | v ∈ w.support}
    w.start_mem_support] at hf
  exact hf
#print axioms Paper7UnicyclicStructure.unicyclic_off_cycle_isAcyclic

end Paper7UnicyclicStructure
