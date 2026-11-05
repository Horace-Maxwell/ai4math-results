import Research.Backfill.Paper7.IntroRootedTreeTerminal

/-! Strengthen the successful terminal existence API by retaining maximal
distance. The new information supports a uniform bound on all nonleaf depths. -/
set_option autoImplicit false
noncomputable section

namespace Paper7IntroTreeDepth
open SimpleGraph

theorem rooted_tree_farthest_terminal_nonleaf
    {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (a : V)
    (hex : ∃ u, u ≠ a ∧ 2 ≤ T.degree u) :
    ∃ x p, x ≠ a ∧ 2 ≤ T.degree x ∧ T.Adj x p ∧
      (∀ j, T.Adj x j → j ≠ p → T.degree j = 1 ∧ j ≠ a) ∧
      ∀ u, u ≠ a → 2 ≤ T.degree u → T.dist a u ≤ T.dist a x := by
  classical
  let U := Finset.univ.filter (fun u : V => u ≠ a ∧ 2 ≤ T.degree u)
  have hU : U.Nonempty := by
    obtain ⟨u, hua, hud⟩ := hex
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hua, hud⟩⟩
  obtain ⟨x, hxU, hmax⟩ := U.exists_max_image (fun u => T.dist a u) hU
  have hx := (Finset.mem_filter.mp hxU).2
  obtain ⟨w, hw, hwd⟩ := hT.connected.exists_path_of_dist a x
  have hwne : ¬w.Nil := SimpleGraph.Walk.not_nil_of_ne hx.1.symm
  refine ⟨x, w.penultimate, hx.1, hx.2, (w.adj_penultimate hwne).symm, ?_, ?_⟩
  · intro j hxj hjp
    have hjw : j ∉ w.support := by
      intro hjw
      exact hjp (hT.isAcyclic.eq_penultimate_of_adj_end hw hxj hjw)
    have hja : j ≠ a := by
      intro hja
      exact hjw (hja.symm ▸ w.start_mem_support)
    have hdist : T.dist a j = T.dist a x + 1 := by
      obtain ⟨q, hq, hqd⟩ := hT.connected.exists_path_of_dist a j
      have he : w.concat hxj = q :=
        (hT.existsUnique_path a j).unique (hw.concat hjw hxj) hq
      have hl : (w.concat hxj).length = T.dist a j :=
        (congrArg (fun p : T.Walk a j => p.length) he).trans hqd
      simpa only [SimpleGraph.Walk.length_concat, hwd] using hl.symm
    have hdlt : T.degree j < 2 := by
      by_contra hn
      have hjU : j ∈ U := Finset.mem_filter.mpr
        ⟨Finset.mem_univ j, hja, Nat.le_of_not_gt hn⟩
      have hm := hmax j hjU
      omega
    have hdpos : 0 < T.degree j := hxj.symm.degree_pos_left
    exact ⟨by omega, hja⟩
  · intro u hua hu
    exact hmax u (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hua, hu⟩)
#print axioms Paper7IntroTreeDepth.rooted_tree_farthest_terminal_nonleaf

theorem rooted_tree_nonleaf_depth_le_two_of_terminal_location
    {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (a : V)
    (hterminal : ∀ x p, x ≠ a → 2 ≤ T.degree x → T.Adj x p →
      (∀ j, T.Adj x j → j ≠ p → T.degree j = 1 ∧ j ≠ a) →
      T.Adj a x ∨ p = a ∨ T.Adj a p) :
    ∀ u, u ≠ a → 2 ≤ T.degree u → T.dist a u ≤ 2 := by
  intro u hua hu
  obtain ⟨x, p, hxa, hx, hxp, hleaf, hmax⟩ :=
    rooted_tree_farthest_terminal_nonleaf T hT a ⟨u, hua, hu⟩
  have hux := hmax u hua hu
  rcases hterminal x p hxa hx hxp hleaf with hax | hpa | hap
  · have hx1 : T.dist a x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hax
    omega
  · subst p
    have hx1 : T.dist a x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxp.symm
    omega
  · have hp1 : T.dist a p = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hap
    have hpx : T.dist p x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxp.symm
    have htri : T.dist a x ≤ T.dist a p + T.dist p x := hT.connected.dist_triangle
    omega
#print axioms Paper7IntroTreeDepth.rooted_tree_nonleaf_depth_le_two_of_terminal_location

end Paper7IntroTreeDepth
