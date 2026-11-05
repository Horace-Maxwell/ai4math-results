import Research.Backfill.Paper7.IntroOffCycleTerminalFourRadiusOne

/-! A genuine three-edge path in the outside tree has depth three. The
original nonleaf-depth theorem then makes its endpoint a true original leaf. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroNonattachmentFour
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroTerminalFourRemote Paper7IntroTreeDepth Paper7UnicyclicAttachment
open Paper7IntroPendantFour

theorem tree_three_edge_endpoint_weight_le_one
    {U : Type} (T : SimpleGraph U) (hT : T.IsTree) (d : U → ℕ)
    (a x y l : U) (hax : T.Adj a x) (hxy : T.Adj x y) (hyl : T.Adj y l)
    (hay : a ≠ y) (hal : a ≠ l) (hxl : x ≠ l)
    (hdepth : ∀ u, u ≠ a → 2 ≤ d u → T.dist a u ≤ 2) : d l ≤ 1 := by
  let p : T.Walk a l := .cons hax (.cons hxy (.cons hyl .nil))
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    change ([a, x, y, l] : List U).Nodup
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · simp only [List.mem_cons, not_or]
      exact ⟨hax.ne, hay, hal, List.not_mem_nil⟩
    · apply List.nodup_cons.mpr
      refine ⟨?_, ?_⟩
      · simp only [List.mem_cons, not_or]
        exact ⟨hxy.ne, hxl, List.not_mem_nil⟩
      · exact List.nodup_cons.mpr
          ⟨by simpa only [List.mem_singleton] using hyl.ne, List.nodup_singleton l⟩
  obtain ⟨q, hq, hqd⟩ := hT.connected.exists_path_of_dist a l
  have he : p = q := (hT.existsUnique_path a l).unique hp hq
  have hl : p.length = T.dist a l := (congrArg (fun t : T.Walk a l => t.length) he).trans hqd
  have hlen : p.length = 3 := rfl
  by_contra hn
  have hd := hdepth l hal.symm (by omega)
  omega
#print axioms Paper7IntroNonattachmentFour.tree_three_edge_endpoint_weight_le_one

theorem intro21_even_degree_four_child_path_leaf
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x y l : C.supp) (hxa : G.Adj x.val.val a.val.val) (hx : G.degree x.val.val = 4)
    (hxy : G.Adj x.val.val y.val.val) (hyl : G.Adj y.val.val l.val.val)
    (hya : y ≠ a) (hlx : l ≠ x) : G.degree l.val.val = 1 := by
  have hthree := intro21_even_degree_four_count_three G b hG hI hn hb x.val.val hx
  obtain ⟨a', c', hac', hdepth⟩ := intro21_even_radius_three_component_nonleaf_depth_le_two
    G b hG hI hn hb hthree r w hw hlen C
  obtain ⟨_pair, _hpair, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  have ha : a' = a := by
    apply Subtype.ext
    exact congrArg Prod.fst ((huniq (a'.val, c') ⟨a'.property, hac'⟩).trans
      (huniq (a.val, c) ⟨a.property, hac⟩).symm)
  subst a'
  have hbridge : ∀ j, G.Adj x.val.val j → G.IsBridge s(x.val.val, j) := by
    intro j hxj
    exact unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen
      x.val.val j x.val.property hxj
  have hla : l ≠ a := by
    intro he
    have hyaAdj : G.Adj y.val.val a.val.val := by simpa only [he] using hyl
    exact bridge_vertex_no_neighbor_triangle G x.val.val hbridge
      a.val.val y.val.val hxa hxy hyaAdj
  have hT : C.toSimpleGraph.IsTree :=
    ⟨C.connected_toSimpleGraph,
      Paper7UnicyclicComponentPaths.connected_component_isAcyclic
        (deleteVertices G {q | q ∈ w.support})
        (Paper7UnicyclicStructure.unicyclic_off_cycle_isAcyclic G b hG r w hw hlen) C⟩
  have hd := tree_three_edge_endpoint_weight_le_one C.toSimpleGraph hT
    (fun u : C.supp => G.degree u.val.val) a x y l hxa.symm hxy hyl
    hya.symm hla.symm hlx.symm hdepth
  have hp := hyl.degree_pos_right
  omega
#print axioms Paper7IntroNonattachmentFour.intro21_even_degree_four_child_path_leaf

end Paper7IntroNonattachmentFour
