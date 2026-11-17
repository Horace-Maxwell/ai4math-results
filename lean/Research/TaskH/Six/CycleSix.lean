import Research.TaskH.Six.Definitions

/-!
Ordered six-vertex witnesses for actual cycles and their original edge sets.
This module makes no new assumptions about the graph or its cycle count.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

def hexagonEdges [DecidableEq V] (f : Fin 6 → V) : Finset (Sym2 V) :=
  {s(f 0, f 1), s(f 1, f 2), s(f 2, f 3), s(f 3, f 4), s(f 4, f 5), s(f 5, f 0)}

def IsHexagon (G : SimpleGraph V) (f : Fin 6 → V) : Prop :=
  Function.Injective f ∧ G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧
    G.Adj (f 2) (f 3) ∧ G.Adj (f 3) (f 4) ∧ G.Adj (f 4) (f 5) ∧ G.Adj (f 5) (f 0)

def hexagonWalk (G : SimpleGraph V) (f : Fin 6 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h45 : G.Adj (f 4) (f 5)) (h50 : G.Adj (f 5) (f 0)) : G.Walk (f 0) (f 0) :=
  .cons h01 (.cons h12 (.cons h23 (.cons h34 (.cons h45 (.cons h50 .nil)))))

theorem hexagonWalk_isCycle (G : SimpleGraph V) (f : Fin 6 → V)
    (hf : Function.Injective f)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h45 : G.Adj (f 4) (f 5)) (h50 : G.Adj (f 5) (f 0)) :
    (hexagonWalk G f h01 h12 h23 h34 h45 h50).IsCycle := by
  rw [hexagonWalk, Walk.cons_isCycle_iff]
  constructor
  · apply Walk.IsPath.mk'
    simp [Walk.support_cons, hf.eq_iff]
  · simp [Walk.edges_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, hf.eq_iff]

theorem hexagonWalk_length (G : SimpleGraph V) (f : Fin 6 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h45 : G.Adj (f 4) (f 5)) (h50 : G.Adj (f 5) (f 0)) :
    (hexagonWalk G f h01 h12 h23 h34 h45 h50).length = 6 := rfl

theorem hexagonWalk_edges [DecidableEq V] (G : SimpleGraph V) (f : Fin 6 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h45 : G.Adj (f 4) (f 5)) (h50 : G.Adj (f 5) (f 0)) :
    (hexagonWalk G f h01 h12 h23 h34 h45 h50).edges.toFinset = hexagonEdges f := by
  simp [hexagonWalk, hexagonEdges, Walk.edges_cons]

theorem hexagonEdges_mem_modCycleEdgeSets [DecidableEq V]
    (f : Fin 6 → V) (hf : IsHexagon G f) :
    hexagonEdges f ∈ ModCycleEdgeSets 6 G := by
  apply Basics.mem_modCycleEdgeSets_iff.mpr
  refine ⟨f 0, hexagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1
    hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2,
    hexagonWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1
      hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2,
    hexagonWalk_edges G f hf.2.1 hf.2.2.1 hf.2.2.2.1
      hf.2.2.2.2.1 hf.2.2.2.2.2.1 hf.2.2.2.2.2.2, ?_⟩
  exact dvd_refl 6

def cycleSixVertices {v : V} (p : G.Walk v v) : Fin 6 → V :=
  fun i => p.getVert i.val

theorem cycleSixVertices_injective {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hl : p.length = 6) :
    Function.Injective (cycleSixVertices p) := by
  intro i j he
  apply Fin.ext
  exact hp.getVert_injOn'
    (by change i.val ≤ p.length - 1; omega)
    (by change j.val ≤ p.length - 1; omega) he

theorem cycleSixVertices_isHexagon {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hl : p.length = 6) :
    IsHexagon G (cycleSixVertices p) := by
  have h6 : p.getVert 6 = v := by simpa only [hl] using p.getVert_length
  refine ⟨cycleSixVertices_injective hp hl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact p.adj_getVert_succ (i := 0) (by omega)
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · exact p.adj_getVert_succ (i := 2) (by omega)
  · exact p.adj_getVert_succ (i := 3) (by omega)
  · exact p.adj_getVert_succ (i := 4) (by omega)
  · change G.Adj (p.getVert 5) (p.getVert 0)
    have ha := p.adj_getVert_succ (i := 5) (by omega : 5 < p.length)
    change G.Adj (p.getVert 5) (p.getVert 6) at ha
    simpa only [h6, Walk.getVert_zero] using ha

theorem six_edges_eq_getVert_list {v : V} {p : G.Walk v v}
    (hl : p.length = 6) :
    p.edges = [s(p.getVert 0, p.getVert 1), s(p.getVert 1, p.getVert 2),
      s(p.getVert 2, p.getVert 3), s(p.getVert 3, p.getVert 4),
      s(p.getVert 4, p.getVert 5), s(p.getVert 5, p.getVert 6)] := by
  apply List.ext_getElem
  · simp only [Walk.length_edges, hl, List.length_cons, List.length_nil]
  · intro i hi _
    rw [Walk.getElem_edges hi]
    have hi6 : i < 6 := by simpa only [Walk.length_edges, hl] using hi
    interval_cases i <;> rfl

theorem cycleSixVertices_hexagonEdges [DecidableEq V] {v : V}
    {p : G.Walk v v} (hl : p.length = 6) :
    hexagonEdges (cycleSixVertices p) = p.edges.toFinset := by
  have h6 : p.getVert 6 = v := by simpa only [hl] using p.getVert_length
  rw [six_edges_eq_getVert_list hl]
  simp [hexagonEdges, cycleSixVertices, h6]

theorem exists_hexagon_of_cycle_length_six [DecidableEq V] {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hl : p.length = 6) :
    ∃ f : Fin 6 → V, IsHexagon G f ∧ hexagonEdges f = p.edges.toFinset :=
  ⟨cycleSixVertices p, cycleSixVertices_isHexagon hp hl,
    cycleSixVertices_hexagonEdges hl⟩

theorem cycleContains_hexagonEdges_iff [DecidableEq V] (f : Fin 6 → V) (v : V) :
    CycleContains (hexagonEdges f) v ↔ ∃ i : Fin 6, f i = v := by
  constructor
  · rintro ⟨e, he, hv⟩
    simp only [hexagonEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [Sym2.mem_iff] at hv
    · rcases hv with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
    · rcases hv with h | h
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    · rcases hv with h | h
      · exact ⟨2, h.symm⟩
      · exact ⟨3, h.symm⟩
    · rcases hv with h | h
      · exact ⟨3, h.symm⟩
      · exact ⟨4, h.symm⟩
    · rcases hv with h | h
      · exact ⟨4, h.symm⟩
      · exact ⟨5, h.symm⟩
    · rcases hv with h | h
      · exact ⟨5, h.symm⟩
      · exact ⟨0, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [CycleContains, hexagonEdges]

theorem cycleVertices_hexagonEdges [Fintype V] [DecidableEq V]
    (f : Fin 6 → V) :
    TaskH.cycleVertices (hexagonEdges f) = Finset.univ.image f := by
  classical
  ext v
  simp only [TaskH.mem_cycleVertices, Finset.mem_image, Finset.mem_univ, true_and]
  exact cycleContains_hexagonEdges_iff f v

theorem cycleVertices_card_six_of_mem [Fintype V] (hs : ShortSixCycles G)
    {s : Finset (Sym2 V)} (hmem : s ∈ ModCycleEdgeSets 6 G) :
    (TaskH.cycleVertices s).card = 6 := by
  classical
  obtain ⟨x, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  have hl := hs p hp hk
  obtain ⟨f, hf, hfe⟩ := exists_hexagon_of_cycle_length_six hp hl
  rw [← he, ← hfe, cycleVertices_hexagonEdges,
    Finset.card_image_of_injective _ hf.1, Finset.card_univ, Fintype.card_fin]

end TaskH.Six

#print axioms TaskH.Six.hexagonEdges
#print axioms TaskH.Six.IsHexagon
#print axioms TaskH.Six.hexagonWalk
#print axioms TaskH.Six.hexagonWalk_isCycle
#print axioms TaskH.Six.hexagonWalk_length
#print axioms TaskH.Six.hexagonWalk_edges
#print axioms TaskH.Six.hexagonEdges_mem_modCycleEdgeSets
#print axioms TaskH.Six.cycleSixVertices
#print axioms TaskH.Six.cycleSixVertices_injective
#print axioms TaskH.Six.cycleSixVertices_isHexagon
#print axioms TaskH.Six.six_edges_eq_getVert_list
#print axioms TaskH.Six.cycleSixVertices_hexagonEdges
#print axioms TaskH.Six.exists_hexagon_of_cycle_length_six
#print axioms TaskH.Six.cycleContains_hexagonEdges_iff
#print axioms TaskH.Six.cycleVertices_hexagonEdges
#print axioms TaskH.Six.cycleVertices_card_six_of_mem
