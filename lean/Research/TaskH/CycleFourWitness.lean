import Research.TaskH.FourCountData

/-!
Every genuine four-cycle has an ordered four-vertex witness. This is the
reverse semantic bridge used for the concrete K5 regression count; the
high-degree lower bound only needs the forward bridge in FourCountData.
-/

universe u

namespace TaskH.FourCount

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem cycle_length_le_card [Fintype V] {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) : p.length ≤ Fintype.card V := by
  have h := hp.support_nodup.length_le_card
  simpa only [List.length_tail, Walk.length_support, Nat.add_sub_cancel] using h

def cycleFourVertices {v : V} (p : G.Walk v v) : Fin 4 → V :=
  fun i => p.getVert i.val

theorem cycleFourVertices_injective {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hl : p.length = 4) :
    Function.Injective (cycleFourVertices p) := by
  intro i j h
  apply Fin.ext
  exact hp.getVert_injOn'
    (by change i.val ≤ p.length - 1; omega)
    (by change j.val ≤ p.length - 1; omega) h

theorem cycleFourVertices_isQuad {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hl : p.length = 4) : IsQuad G (cycleFourVertices p) := by
  have h4 : p.getVert 4 = v := by simpa only [hl] using p.getVert_length
  refine ⟨cycleFourVertices_injective hp hl, ?_, ?_, ?_, ?_⟩
  · exact p.adj_getVert_succ (i := 0) (by omega)
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · exact p.adj_getVert_succ (i := 2) (by omega)
  · change G.Adj (p.getVert 3) (p.getVert 0)
    have ha := p.adj_getVert_succ (i := 3) (by omega : 3 < p.length)
    change G.Adj (p.getVert 3) (p.getVert 4) at ha
    simpa only [h4, Walk.getVert_zero] using ha

theorem four_edges_eq_getVert_list {v : V} {p : G.Walk v v}
    (hl : p.length = 4) :
    p.edges = [s(p.getVert 0, p.getVert 1), s(p.getVert 1, p.getVert 2),
      s(p.getVert 2, p.getVert 3), s(p.getVert 3, p.getVert 4)] := by
  apply List.ext_getElem
  · simp only [Walk.length_edges, hl, List.length_cons, List.length_nil]
  · intro i hi _
    rw [Walk.getElem_edges hi]
    have hi4 : i < 4 := by simpa only [Walk.length_edges, hl] using hi
    interval_cases i <;> rfl

theorem cycleFourVertices_quadEdges [DecidableEq V] {v : V} {p : G.Walk v v}
    (hl : p.length = 4) :
    quadEdges (cycleFourVertices p) = p.edges.toFinset := by
  have h4 : p.getVert 4 = v := by simpa only [hl] using p.getVert_length
  rw [four_edges_eq_getVert_list hl]
  simp [quadEdges, cycleFourVertices, h4]

theorem exists_quad_of_cycle_length_four [DecidableEq V] {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hl : p.length = 4) :
    ∃ f : Fin 4 → V, IsQuad G f ∧ quadEdges f = p.edges.toFinset :=
  ⟨cycleFourVertices p, cycleFourVertices_isQuad hp hl,
    cycleFourVertices_quadEdges hl⟩

theorem length_four_of_mod_four_of_card_le_seven [Fintype V] {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hk : 4 ∣ p.length)
    (hn : Fintype.card V ≤ 7) : p.length = 4 := by
  have hl := cycle_length_le_card hp
  have hp3 := hp.three_le_length
  obtain ⟨t, ht⟩ := hk
  omega

theorem mem_modCycleEdgeSets_iff_mem_image_quadWords [Fintype V] [DecidableEq V]
    (hn : Fintype.card V ≤ 7) {s : Finset (Sym2 V)} :
    s ∈ Challenge.ModCycleEdgeSets 4 G ↔ s ∈ (quadWords G).image quadEdges := by
  classical
  constructor
  · intro hs
    obtain ⟨v, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hs
    have hl := length_four_of_mod_four_of_card_le_seven hp hk hn
    obtain ⟨f, hf, hfe⟩ := exists_quad_of_cycle_length_four hp hl
    exact Finset.mem_image.mpr ⟨f,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, hfe.trans he⟩
  · intro hs
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hs
    rw [← hfe]
    exact quadEdges_mem_modCycleEdgeSets G f (Finset.mem_filter.mp hf).2

theorem modCycleCount_eq_image_quadWords_card [Fintype V] [DecidableEq V]
    (hn : Fintype.card V ≤ 7) :
    Challenge.modCycleCount 4 G = ((quadWords G).image quadEdges).card := by
  classical
  have he : Challenge.ModCycleEdgeSets 4 G =
      (((quadWords G).image quadEdges : Finset (Finset (Sym2 V))) : Set (Finset (Sym2 V))) := by
    ext s
    exact mem_modCycleEdgeSets_iff_mem_image_quadWords hn
  rw [Challenge.modCycleCount, he, Set.ncard_coe_finset]

/-- A fixed, computable family for the independent K5 regression. -/
def completeFiveQuadWords : Finset (Fin 4 → Fin 5) :=
  Finset.univ.filter Function.Injective

def completeFiveCycleEdgeSets : Finset (Finset (Sym2 (Fin 5))) :=
  completeFiveQuadWords.image quadEdges

theorem completeFiveCycleEdgeSets_card : completeFiveCycleEdgeSets.card = 15 := by
  decide +kernel

theorem quadWords_completeFive : quadWords (⊤ : SimpleGraph (Fin 5)) =
    completeFiveQuadWords := by
  classical
  ext f
  simp only [quadWords, completeFiveQuadWords, Finset.mem_filter, Finset.mem_univ,
    true_and, IsQuad, SimpleGraph.top_adj]
  constructor
  · exact And.left
  · intro hf
    exact ⟨hf, hf.ne (by decide), hf.ne (by decide),
      hf.ne (by decide), hf.ne (by decide)⟩

theorem completeFive_modCycleCount :
    Challenge.modCycleCount 4 (⊤ : SimpleGraph (Fin 5)) = 15 := by
  rw [modCycleCount_eq_image_quadWords_card (by decide), quadWords_completeFive]
  exact completeFiveCycleEdgeSets_card

end TaskH.FourCount

#print axioms TaskH.FourCount.cycle_length_le_card
#print axioms TaskH.FourCount.exists_quad_of_cycle_length_four
#print axioms TaskH.FourCount.modCycleCount_eq_image_quadWords_card
#print axioms TaskH.FourCount.completeFiveCycleEdgeSets_card
#print axioms TaskH.FourCount.completeFive_modCycleCount
