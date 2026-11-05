import Mathlib

/-! A finite rooted tree has a terminal nonleaf whenever a nonleaf occurs
away from its root. No bound on branching is imposed. -/
set_option autoImplicit false
noncomputable section

namespace Paper7IntroTerminalExistence
open SimpleGraph

private theorem tree_path_length_eq_dist
    {V : Type} (T : SimpleGraph V) (hT : T.IsTree)
    {a x : V} (p : T.Walk a x) (hp : p.IsPath) : p.length = T.dist a x := by
  obtain ⟨q, hq, hqd⟩ := hT.connected.exists_path_of_dist a x
  have he : p = q := (hT.existsUnique_path a x).unique hp hq
  simpa only [he] using hqd

theorem rooted_tree_terminal_nonleaf_exists
    {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (a : V)
    (hex : ∃ u, u ≠ a ∧ 2 ≤ T.degree u) :
    ∃ x p, x ≠ a ∧ 2 ≤ T.degree x ∧ T.Adj x p ∧
      ∀ j, T.Adj x j → j ≠ p → T.degree j = 1 ∧ j ≠ a := by
  classical
  let U := Finset.univ.filter (fun u : V => u ≠ a ∧ 2 ≤ T.degree u)
  have hU : U.Nonempty := by
    obtain ⟨u, hua, hud⟩ := hex
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hua, hud⟩⟩
  obtain ⟨x, hxU, hmax⟩ := U.exists_max_image (fun u => T.dist a u) hU
  have hx := (Finset.mem_filter.mp hxU).2
  obtain ⟨w, hw, hwd⟩ := hT.connected.exists_path_of_dist a x
  have hwne : ¬w.Nil := SimpleGraph.Walk.not_nil_of_ne hx.1.symm
  refine ⟨x, w.penultimate, hx.1, hx.2, (w.adj_penultimate hwne).symm, ?_⟩
  intro j hxj hjp
  have hjw : j ∉ w.support := by
    intro hjw
    exact hjp (hT.isAcyclic.eq_penultimate_of_adj_end hw hxj hjw)
  have hja : j ≠ a := by
    intro hja
    exact hjw (hja.symm ▸ w.start_mem_support)
  have hdist : T.dist a j = T.dist a x + 1 := by
    have he := tree_path_length_eq_dist T hT (w.concat hxj) (hw.concat hjw hxj)
    simpa only [SimpleGraph.Walk.length_concat, hwd] using he.symm
  have hdlt : T.degree j < 2 := by
    by_contra hn
    have hjU : j ∈ U := Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hja, Nat.le_of_not_gt hn⟩
    have hm := hmax j hjU
    omega
  have hdpos : 0 < T.degree j := hxj.symm.degree_pos_left
  exact ⟨by omega, hja⟩
#print axioms Paper7IntroTerminalExistence.rooted_tree_terminal_nonleaf_exists

end Paper7IntroTerminalExistence
