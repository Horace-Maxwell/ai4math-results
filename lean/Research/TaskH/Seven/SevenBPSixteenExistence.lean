import Research.TaskH.Seven.SevenBPEighteenExclusion45

/-! A genuine sixteen-cycle in the original nonempty bipartite graph at
order at most45 and minimum degree7, conditional only on no fourteen-cycle.
The internal absence-of-sixteen premise is discharged by contradiction. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem exists_cycle_sixteen_of_card_le_forty_five [Nonempty V]
    (hb : G.IsBipartite) (hn45 : Fintype.card V≤45)
    (hd : ∀x : V,7≤G.degree x) (h14 : NoFourteenCycle G) :
    ∃(a : V)(p : G.Walk a a),p.IsCycle ∧ p.length=16 := by
  by_contra hnot
  have h16 : NoSixteenCycle G := by
    intro a p hp hl
    exact hnot ⟨a,p,hp,hl⟩
  obtain ⟨a,p,hp,hl⟩ := exists_cycle_sixteen_or_eighteen hb (by omega) hd h14
  rcases hl with hl | hl
  · exact hnot ⟨a,p,hp,hl⟩
  · exact no_eighteen_walk_of_card_le_forty_five hb h14 h16 hd hn45 p hp hl

theorem exists_isCycleSixteen_of_card_le_forty_five [Nonempty V]
    (hb : G.IsBipartite) (hn45 : Fintype.card V≤45)
    (hd : ∀x : V,7≤G.degree x) (h14 : NoFourteenCycle G) :
    ∃u : Fin 16 → V,IsCycleSixteen G u := by
  obtain ⟨a,p,hp,hl⟩ := exists_cycle_sixteen_of_card_le_forty_five hb hn45 hd h14
  exact ⟨cycleSixteenVertices p,cycleSixteenVertices_isCycleSixteen hp hl⟩

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.exists_cycle_sixteen_of_card_le_forty_five
#print axioms TaskH.Seven.BP.exists_isCycleSixteen_of_card_le_forty_five
