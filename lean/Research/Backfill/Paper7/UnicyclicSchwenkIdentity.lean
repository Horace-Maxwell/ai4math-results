import Research.Backfill.Paper7.TreePathCofactor
import Research.Backfill.Paper7.UnicyclicCyclePath

/-! The exact original finite-graph Schwenk contract. The cycle, edge and
both vertex deletion sets are the actual objects in the frozen statement. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open SimpleGraph BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

theorem check_UnicyclicSchwenkIdentity :
    BackfillPaper7.Challenge.Legacy.Algebra.UnicyclicSchwenkIdentity := by
  intro V fV dV G aG b hG r w hw hlen u v he
  let T := G.deleteEdges ({s(u,v)} : Set (Sym2 V))
  let aT : DecidableRel T.Adj := inferInstance
  have hT : T.IsTree := @cycle_edge_deleted_tree V dV G b hG r w hw hlen u v he
  obtain ⟨p, hp, _hsupport⟩ := @exists_cycle_cut_path V dV G r w hw u v he
  have ht := @tree_path_cofactor V fV dV T aT hT u v p hp
  have hc := @cut_tree_path_complement_phi V fV dV G aG b hG r w hw hlen u v he p hp
  have hbase := @graphPhi_edge_adjugate V fV dV G aG u v (w.edges_subset_edgeSet he)
  dsimp only at hbase
  refine hbase.trans ?_
  apply congrArg₂ (fun A B : Polynomial ℤ => A - B)
  · apply congrArg₂ (fun A B : Polynomial ℤ => A - B)
    · exact graphPhi_instances_eq _ _ _ _ _
    · exact graphPhi_instances_eq _ _ _ _ _
  · apply congrArg (fun z : Polynomial ℤ => 2 * z)
    refine (graphCofactor_instances_eq _ fV _ dV T _ aT v u).trans ?_
    refine ht.trans ?_
    exact (graphPhi_instances_eq _ _ _ _ _).trans
      (hc.trans (graphPhi_instances_eq _ _ _ _ _))
#print axioms Paper7UnicyclicSchwenk.check_UnicyclicSchwenkIdentity

end Paper7UnicyclicSchwenk
