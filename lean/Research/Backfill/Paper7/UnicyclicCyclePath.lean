import Research.Backfill.Paper7.SchwenkGraphExpansion
import Research.Backfill.Paper7.UnicyclicCardinality
import Research.Backfill.Paper7.CycleFirstDart

/-! Actual cycle-edge deletion produces a tree, and its unique path between
those endpoints has exactly the support of the supplied cycle walk. -/
set_option autoImplicit false
noncomputable section
namespace Paper7UnicyclicSchwenk
open SimpleGraph BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped Classical

theorem cycle_support_eq_of_edgeFinset {V : Type} [DecidableEq V]
    {G : SimpleGraph V} {r s : V} (w : G.Walk r r) (c : G.Walk s s)
    (hw : w.IsCycle) (hc : c.IsCycle) (he : w.edges.toFinset = c.edges.toFinset) :
    {z | z ∈ w.support} = {z | z ∈ c.support} := by
  ext z
  constructor
  · intro hz
    obtain ⟨e, hew, hze⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hw.not_nil).mp hz
    apply (Walk.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mpr
    refine ⟨e, ?_, hze⟩
    exact List.mem_toFinset.mp (he ▸ List.mem_toFinset.mpr hew)
  · intro hz
    obtain ⟨e, hec, hze⟩ := (Walk.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hz
    apply (Walk.mem_support_iff_exists_mem_edges_of_not_nil hw.not_nil).mpr
    refine ⟨e, ?_, hze⟩
    exact List.mem_toFinset.mp (he.symm ▸ List.mem_toFinset.mpr hec)
#print axioms Paper7UnicyclicSchwenk.cycle_support_eq_of_edgeFinset

/-- This support construction uses an actual rotated/oriented cycle and its
actual tail, rather than an abstract subset of the vertices. -/
theorem exists_cycle_cut_path {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (r : V) (w : G.Walk r r) (hw : w.IsCycle)
    (u v : V) (he : s(u,v) ∈ w.edges) :
    ∃ p : (G.deleteEdges ({s(u,v)} : Set (Sym2 V))).Walk v u,
      p.IsPath ∧ {z | z ∈ p.support} = {z | z ∈ w.support} := by
  have huv : G.Adj u v := w.edges_subset_edgeSet he
  let d : G.Dart := ⟨(u,v), huv⟩
  obtain ⟨c, hc, _hlen, hedge, hsnd⟩ :=
    Paper7Cycles.cycle_with_first_dart w hw d he
  have hsupp : {z | z ∈ c.support} = {z | z ∈ w.support} :=
    cycle_support_eq_of_edgeFinset c w hc hw hedge
  change c.snd = v at hsnd
  cases c with
  | nil => exact (hc.ne_nil rfl).elim
  | @cons _ x _ hux p =>
    have hx : x = v := by simpa only [Walk.snd_cons] using hsnd
    subst x
    have hp := (Walk.cons_isCycle_iff p hux).mp hc
    refine ⟨p.toDeleteEdge s(u,v) hp.2, ?_, ?_⟩
    · simpa only [Walk.isPath_transfer] using hp.1
    · have htail : {z | z ∈ p.support} = {z | z ∈ (Walk.cons hux p).support} := by
        ext z
        simp only [Set.mem_ofPred_eq, Walk.support_cons, List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | hz)
          · exact p.end_mem_support
          · exact hz
      simpa only [Walk.support_transfer] using htail.trans hsupp
#print axioms Paper7UnicyclicSchwenk.exists_cycle_cut_path

theorem cycle_edge_deleted_tree {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (u v : V) (he : s(u,v) ∈ w.edges) :
    (G.deleteEdges ({s(u,v)} : Set (Sym2 V))).IsTree := by
  exact Paper7Unicyclic.unicyclic_delete_cycle_edge_isTree hG
    ⟨r, w, hw, hlen, rfl⟩ (List.mem_toFinset.mpr he)
#print axioms Paper7UnicyclicSchwenk.cycle_edge_deleted_tree

/-- Every path between the specified endpoints in the deleted-edge tree has
precisely the original cycle support. -/
theorem cut_tree_path_support {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (b : ℕ) (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (u v : V) (he : s(u,v) ∈ w.edges)
    (p : (G.deleteEdges ({s(u,v)} : Set (Sym2 V))).Walk v u) (hp : p.IsPath) :
    {z | z ∈ p.support} = {z | z ∈ w.support} := by
  obtain ⟨q, hq, hsupp⟩ := exists_cycle_cut_path G r w hw u v he
  have ht := cycle_edge_deleted_tree G b hG r w hw hlen u v he
  have heq : p = q := ExistsUnique.unique (ht.existsUnique_path v u) hp hq
  rw [heq]
  exact hsupp
#print axioms Paper7UnicyclicSchwenk.cut_tree_path_support

/-- Deleting the tree path retains exactly the graph from deleting the
original cycle support, including all detached branches and empty complements. -/
theorem cut_tree_path_complement_phi {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ) (hG : IsUnicyclicWithCycle G b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (u v : V) (he : s(u,v) ∈ w.edges)
    (p : (G.deleteEdges ({s(u,v)} : Set (Sym2 V))).Walk v u) (hp : p.IsPath) :
    graphPhi (deleteVertices (G.deleteEdges ({s(u,v)} : Set (Sym2 V)))
      {z | z ∈ p.support}) = graphPhi (deleteVertices G {z | z ∈ w.support}) := by
  have hs := cut_tree_path_support G b hG r w hw hlen u v he p hp
  have hm (z : V) : z ∈ p.support ↔ z ∈ w.support := Set.ext_iff.mp hs z
  let T := G.deleteEdges ({s(u,v)} : Set (Sym2 V))
  let A := deleteVertices T {z | z ∈ p.support}
  let B := deleteVertices T {z | z ∈ w.support}
  let e : {z : V // z ∉ p.support} ≃ {z : V // z ∉ w.support} :=
    { toFun := fun z => ⟨z.val, fun hz => z.property ((hm z.val).mpr hz)⟩
      invFun := fun z => ⟨z.val, fun hz => z.property ((hm z.val).mp hz)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  let ei : A ≃g B :=
    { toEquiv := e
      map_rel_iff' := Iff.rfl }
  have hphi : graphPhi A = graphPhi B := by
    calc
      graphPhi A = (A.adjMatrix ℤ).charpoly := Paper7GraphPhi.graphPhi_eq_charpoly A
      _ = (B.adjMatrix ℤ).charpoly :=
        (Matrix.charpoly_reindex ei.toEquiv (A.adjMatrix ℤ)).symm.trans
          (congrArg Matrix.charpoly (ei.reindex_adjMatrix ℤ))
      _ = graphPhi B := (Paper7GraphPhi.graphPhi_eq_charpoly B).symm
  have hdel := deleteVertices_deleteEdge G u v {z | z ∈ w.support}
    (w.fst_mem_support_of_mem_edges he)
  exact hphi.trans (congrArg
    (fun H : SimpleGraph {z : V // z ∉ w.support} => graphPhi H) hdel)

#print axioms Paper7UnicyclicSchwenk.cut_tree_path_complement_phi

end Paper7UnicyclicSchwenk
