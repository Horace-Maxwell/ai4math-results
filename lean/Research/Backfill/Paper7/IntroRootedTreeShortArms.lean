import Research.Backfill.Paper7.IntroTreeTerminalDepth
import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment

/-! If every terminal nonleaf of a finite rooted tree has degree two and
parent equal to the root, all nonroot nonleaves are adjacent to the root
and have degree two. No bound on branching is assumed. -/
set_option autoImplicit false
noncomputable section

namespace Paper7IntroNonattachmentThree
open SimpleGraph Paper7IntroTreeDepth Paper7IntroPendantFour

theorem rooted_tree_short_arms_of_terminal_parent_root
    {U : Type} [Fintype U] [DecidableEq U]
    (T : SimpleGraph U) [DecidableRel T.Adj] (hT : T.IsTree) (a : U)
    (hterminal : ∀ x p, x ≠ a → 2 ≤ T.degree x → T.Adj x p →
      (∀ j, T.Adj x j → j ≠ p → T.degree j = 1 ∧ j ≠ a) →
      T.degree x = 2 ∧ p = a) :
    ∀ u, u ≠ a → T.degree u ≤ 2 ∧ (2 ≤ T.degree u → T.Adj u a) := by
  have hnear : ∀ u, u ≠ a → 2 ≤ T.degree u → T.Adj u a := by
    intro u hua hu
    obtain ⟨x, p, hxa, hx, hxp, hleaf, hmax⟩ :=
      rooted_tree_farthest_terminal_nonleaf T hT a ⟨u, hua, hu⟩
    have hpa := (hterminal x p hxa hx hxp hleaf).2
    have hxaAdj : T.Adj x a := hpa ▸ hxp
    have hx1 : T.dist a x = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hxaAdj.symm
    have hle := hmax u hua hu
    have hpos := hT.connected.pos_dist_of_ne hua.symm
    have hu1 : T.dist a u = 1 := by omega
    exact (SimpleGraph.dist_eq_one_iff_adj.mp hu1).symm
  intro u hua
  refine ⟨?_, hnear u hua⟩
  by_cases hu : 2 ≤ T.degree u
  · have huaAdj := hnear u hua hu
    have hleaf : ∀ j, T.Adj u j → j ≠ a → T.degree j = 1 ∧ j ≠ a := by
      intro j huj hja
      have hjlt : T.degree j < 2 := by
        by_contra hjnot
        have hjaAdj := hnear j hja (by omega)
        exact bridge_vertex_no_neighbor_triangle T u
          (fun v huv => SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic huv)
          a j huaAdj huj hjaAdj
      have hjpos := huj.degree_pos_right
      exact ⟨by omega, hja⟩
    exact (hterminal u a hua hu huaAdj hleaf).1.le
  · omega
#print axioms Paper7IntroNonattachmentThree.rooted_tree_short_arms_of_terminal_parent_root

end Paper7IntroNonattachmentThree
