import Research.TaskH.Seven.SevenK5LastClosed

/-! Actual original graph K5 exclusion. Every numeric/group/tuple premise of
the last branch is derived internally from the original equality graph. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem equality_cliqueFree_five (hcrit : IsCriticalPlus 7 G)
    (hc : modCycleCount 7 G = 2880) (hnot : ¬ IsCompleteOfOrder G 8) : G.CliqueFree 5 := by
  classical
  have hs : ShortSevenCycles G := equality_shortSevenCycles hcrit hc
  have hr : RainbowSevenCycles G := equality_rainbowSevenCycles hcrit hc
  have hn9 := noncomplete_card_ge_nine hcrit hs hr hnot
  have hn51 := critical_card_le_fifty_one hcrit hs hr hn9 hc
  have hd : ∀ x : V, 10 ≤ G.degree x := fun x =>
    equality_noncomplete_degree_ge_ten hcrit hc hnot x
  by_contra hfree
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hfree
  have he : Function.Injective e := e.injective
  have hclique : ∀ i j : Fin 5, i ≠ j → G.Adj (e i) (e j) := by
    intro i j hij
    exact e.map_rel_iff.mpr (by simpa using hij)
  have hM := (equality_fiveClique_all_active_no_multi hcrit hc hnot e he hclique).2
  have hn55 := critical_five_clique_no_multi_packing hcrit hr hn9 e he hclique hd hM
  omega

theorem equality_noncomplete_degree_ge_eleven (hcrit : IsCriticalPlus 7 G)
    (hc : modCycleCount 7 G = 2880) (hnot : ¬ IsCompleteOfOrder G 8) (v : V) :
    11 ≤ G.degree v :=
  critical_degree_ge_eleven_of_cliqueFree_five hcrit (equality_shortSevenCycles hcrit hc)
    (equality_rainbowSevenCycles hcrit hc) (equality_cliqueFree_five hcrit hc hnot) v

end TaskH.Seven
#print axioms TaskH.Seven.equality_cliqueFree_five
#print axioms TaskH.Seven.equality_noncomplete_degree_ge_eleven
