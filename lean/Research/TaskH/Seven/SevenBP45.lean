import Research.TaskH.Seven.SevenBPSixteenEndgame
import Research.TaskH.Seven.SevenBPSixteenExistence

/-! The original standalone BP45 conclusion on the original graph: a
nonempty finite simple bipartite graph of order<=45 and minimum degree>=7
has an actual simple14-cycle. No auxiliary side/count premise remains. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem bipartite_card_le_forty_five_exists_fourteen [Nonempty V]
    (hb : G.IsBipartite) (hn45 : Fintype.card V≤45) (hd : ∀z : V,7≤G.degree z) :
    ∃(a : V)(p : G.Walk a a),p.IsCycle ∧ p.length=14 := by
  by_contra hnot
  have h14 : NoFourteenCycle G := by
    intro a p hp hl
    exact hnot ⟨a,p,hp,hl⟩
  obtain ⟨u,hu⟩ := exists_isCycleSixteen_of_card_le_forty_five hb hn45 hd h14
  exact sixteen_actual_cycle_impossible_at_order_forty_five hb u hu hn45 hd h14

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.bipartite_card_le_forty_five_exists_fourteen
