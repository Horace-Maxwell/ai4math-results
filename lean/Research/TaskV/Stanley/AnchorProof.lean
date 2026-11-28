import Research.TaskV.Stanley.AnchorVertexWeights
import Research.TaskV.Stanley.AnchorTerminals
import Research.TaskV.Stanley.ExpandCore

namespace StanleyContinuation
open SimpleGraph Finset
noncomputable section

/-- Ordinary chromatic symmetric functions distinguish every tree in the frozen anchor class
from every nonisomorphic finite tree. -/
theorem anchorReconstruction : AnchorReconstruction := by
  classical
  intro n m G H tg th anchors same
  obtain ⟨A,incl,eqv,_,cover,weights,profiles⟩ := anchorCutProfiles_of_sameCSF tg th anchors same
  let a (j : ↥A) : ↥(core G) := ⟨j.val,incl j.property⟩
  let b (j : ↥A) : ↥(core H) := eqv (a j)
  let w (x : ↥(core G)) := coreWeight G x
  let z (x : ↥(core H)) := coreWeight H x
  have cg := Finset.card_pos.mp (by have := anchors.1; omega : 0 < (core G).card)
  obtain ⟨v,hv⟩ := cg
  have ch : (core H).Nonempty := ⟨(eqv ⟨v,hv⟩).val,(eqv ⟨v,hv⟩).property⟩
  have treeG := coreGraph_tree tg ⟨v,hv⟩
  have treeH := coreGraph_tree th ch
  have tag_terminal (x : ↥(core G)) (h : ∃! y, (coreGraph G).Adj x y) : x.val ∈ A :=
    cover _ x.property ((core_terminal_iff_count x).mp h)
  have hits : cutsMeetMarks (coreGraph G) a := by
    intro s side
    obtain ⟨x,xs,term⟩ := terminal_in_cut treeG side
    exact ⟨⟨x.val,tag_terminal x term⟩,xs⟩
  have : Nontrivial ↥(core G) := Fintype.one_lt_card_iff_nontrivial.mp
    (by rw [Fintype.card_coe]; have hc := anchors.1; omega)
  obtain ⟨u,du⟩ := treeG.exists_vert_degree_one_of_nontrivial
  let root : ↥A := ⟨u.val,tag_terminal u ((coreGraph G).degree_eq_one_iff_existsUnique_adj.mp du)⟩
  have total : ∑ x, w x = ∑ y, z y := by
    calc
      _ = ∑ x, z (eqv x) := sum_congr rfl (fun x _ => (weights x).symm)
      _ = _ := eqv.sum_comp z
  obtain ⟨e,code,order⟩ := matching_record_order treeG treeH w z
    (fun x => by simp [w, coreWeight]) (fun x => by simp [z, coreWeight]) a b root hits profiles total
  let f := liftRecordEquiv treeG treeH (a root) (b root) e
  let iso : coreGraph G ≃g coreGraph H :=
    { toEquiv := f
      map_rel_iff' := fun {x y} => (reconstruct_core_adj treeG treeH _ _ e order x y).symm }
  have mass (s : RootedRecords (coreGraph G) (a root)) :
      (∑ y ∈ (e s).val, z y) = ∑ x ∈ s.val, w x := congrArg Prod.fst (code s)
  exact expand_weighted_core_iso tg.connected th.connected ⟨v,hv⟩ ch iso
    (weights_of_record_sums treeG treeH _ _ w z e order mass)

end
end StanleyContinuation
