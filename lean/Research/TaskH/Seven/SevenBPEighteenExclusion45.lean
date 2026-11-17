import Research.TaskH.Seven.SevenBPEighteenSideCounts

/-! The original order45 bipartite problem needs no order49 extreme-case
covering argument. Both genuine outside sides have at least15 vertices,
whereas an18-cycle leaves at most27 vertices outside at order at most45. -/
set_option autoImplicit false
universe u
namespace TaskH.Seven.BP
open SimpleGraph
open scoped Classical
variable {V : Type u} {G : SimpleGraph V}

def cycleEighteenVertices {a : V} (p : G.Walk a a) : Fin 18 → V :=
  fun i => p.getVert i.val

theorem cycleEighteenVertices_isCycleEighteen {a : V} {p : G.Walk a a}
    (hp : p.IsCycle) (hl : p.length=18) : IsCycleEighteen G (cycleEighteenVertices p) := by
  constructor
  · intro i j he
    apply Fin.ext
    exact hp.getVert_injOn'
      (by change i.val≤p.length-1; omega)
      (by change j.val≤p.length-1; omega) he
  · intro i
    have h18 : p.getVert 18=a := by simpa only [hl] using p.getVert_length
    fin_cases i
    · exact p.adj_getVert_succ (i := 0) (by omega)
    · exact p.adj_getVert_succ (i := 1) (by omega)
    · exact p.adj_getVert_succ (i := 2) (by omega)
    · exact p.adj_getVert_succ (i := 3) (by omega)
    · exact p.adj_getVert_succ (i := 4) (by omega)
    · exact p.adj_getVert_succ (i := 5) (by omega)
    · exact p.adj_getVert_succ (i := 6) (by omega)
    · exact p.adj_getVert_succ (i := 7) (by omega)
    · exact p.adj_getVert_succ (i := 8) (by omega)
    · exact p.adj_getVert_succ (i := 9) (by omega)
    · exact p.adj_getVert_succ (i := 10) (by omega)
    · exact p.adj_getVert_succ (i := 11) (by omega)
    · exact p.adj_getVert_succ (i := 12) (by omega)
    · exact p.adj_getVert_succ (i := 13) (by omega)
    · exact p.adj_getVert_succ (i := 14) (by omega)
    · exact p.adj_getVert_succ (i := 15) (by omega)
    · exact p.adj_getVert_succ (i := 16) (by omega)
    · change G.Adj (p.getVert 17) (p.getVert 0)
      have ha := p.adj_getVert_succ (i := 17) (by omega : 17<p.length)
      change G.Adj (p.getVert 17) (p.getVert 18) at ha
      simpa only [h18,Walk.getVert_zero] using ha

theorem no_eighteen_of_card_le_forty_five [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G) (u : Fin 18 → V)
    (hu : IsCycleEighteen G u) (hd : ∀x : V,7≤G.degree x) (hn45 : Fintype.card V≤45) :
    False := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  have hn49 : Fintype.card V≤49 := by omega
  have h0 := eighteen_each_side_at_least_fifteen hb h14 h16 u hu hn49 hd c 0
  have h1 := eighteen_each_side_at_least_fifteen hb h14 h16 u hu hn49 hd c 1
  have hsum := eighteen_outside_sides_card c u hu
  omega

theorem no_eighteen_walk_of_card_le_forty_five [Fintype V] (hb : G.IsBipartite)
    (h14 : NoFourteenCycle G) (h16 : NoSixteenCycle G)
    (hd : ∀x : V,7≤G.degree x) (hn45 : Fintype.card V≤45)
    {a : V} (p : G.Walk a a) (hp : p.IsCycle) : p.length≠18 := by
  intro hl
  exact no_eighteen_of_card_le_forty_five hb h14 h16 (cycleEighteenVertices p)
    (cycleEighteenVertices_isCycleEighteen hp hl) hd hn45

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.cycleEighteenVertices
#print axioms TaskH.Seven.BP.cycleEighteenVertices_isCycleEighteen
#print axioms TaskH.Seven.BP.no_eighteen_of_card_le_forty_five
#print axioms TaskH.Seven.BP.no_eighteen_walk_of_card_le_forty_five
