import Research.TaskV.Stanley.PeelInduction
import Research.TaskV.Stanley.AnchorTerminals
import Research.TaskV.Stanley.ExpandCore

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

private theorem repeated_core_leaf {n : ℕ} {G : SimpleGraph (Fin n)} (x : ↥(core G))
    (bad : repeatedLeaf (coreGraph G) (fun v => coreWeight G v) x) : untaggedCoreLeaf G x := by
  obtain ⟨terminal,y,ne,sameWeight⟩ := bad
  exact ⟨x.property,(core_terminal_iff_count x).mp terminal,y.val,y.property,
    fun h => ne (Subtype.ext h),sameWeight⟩

/-- The ordinary chromatic symmetric function determines each tree in the frozen peeling class
among all finite trees. -/
theorem peelingReconstruction : PeelingReconstruction := by
  classical
  intro n m G H tree tree' pw same
  have hn : 2 ≤ n := pw.1.trans (by simpa only [Fintype.card_fin] using card_le_univ (core G))
  have cg : (core G).Nonempty := card_pos.mp (by have := pw.1; omega)
  obtain ⟨a,ha⟩ := cg
  obtain ⟨e,_⟩ := coreWeights_of_sameCSF tree tree' hn pw.2.1 same
  have ch : (core H).Nonempty := ⟨(e ⟨a,ha⟩).val,(e ⟨a,ha⟩).property⟩
  have few : atMostOneRepeatedLeaf (coreGraph G) (fun v => coreWeight G v) :=
    fun x y hx hy => Subtype.ext (pw.2.2.2 x.val y.val (repeated_core_leaf x hx) (repeated_core_leaf y hy))
  obtain ⟨f,colors⟩ := colored_tree_reconstruction (coreGraph_tree tree ⟨a,ha⟩)
    (coreGraph_tree tree' ch) few (peel_coloredSets_of_sameCSF tree tree' pw same)
  exact expand_weighted_core_iso tree.connected tree'.connected ⟨a,ha⟩ ch f colors

end
end StanleyContinuation
