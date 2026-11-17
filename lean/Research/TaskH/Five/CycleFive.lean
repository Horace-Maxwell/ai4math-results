import Research.TaskH.Five.Definitions

/-!
Ordered five-vertex witnesses for actual cycles and their frozen edge sets.
The original modulo-five collection is retained throughout.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

def pentagonEdges [DecidableEq V] (f : Fin 5 → V) : Finset (Sym2 V) :=
  {s(f 0, f 1), s(f 1, f 2), s(f 2, f 3), s(f 3, f 4), s(f 4, f 0)}

def IsPentagon (G : SimpleGraph V) (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧
    G.Adj (f 2) (f 3) ∧ G.Adj (f 3) (f 4) ∧ G.Adj (f 4) (f 0)

def pentagonWalk (G : SimpleGraph V) (f : Fin 5 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h40 : G.Adj (f 4) (f 0)) : G.Walk (f 0) (f 0) :=
  .cons h01 (.cons h12 (.cons h23 (.cons h34 (.cons h40 .nil))))

theorem pentagonWalk_isCycle (G : SimpleGraph V) (f : Fin 5 → V)
    (hf : Function.Injective f)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h40 : G.Adj (f 4) (f 0)) :
    (pentagonWalk G f h01 h12 h23 h34 h40).IsCycle := by
  rw [pentagonWalk, Walk.cons_isCycle_iff]
  constructor
  · apply Walk.IsPath.mk'
    simp [Walk.support_cons, hf.eq_iff]
  · simp [Walk.edges_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, hf.eq_iff]

theorem pentagonWalk_length (G : SimpleGraph V) (f : Fin 5 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h40 : G.Adj (f 4) (f 0)) :
    (pentagonWalk G f h01 h12 h23 h34 h40).length = 5 := rfl

theorem pentagonWalk_edges [DecidableEq V] (G : SimpleGraph V) (f : Fin 5 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h40 : G.Adj (f 4) (f 0)) :
    (pentagonWalk G f h01 h12 h23 h34 h40).edges.toFinset = pentagonEdges f := by
  simp [pentagonWalk, pentagonEdges, Walk.edges_cons]

theorem pentagonEdges_mem_modCycleEdgeSets [DecidableEq V]
    (f : Fin 5 → V) (hf : IsPentagon G f) :
    pentagonEdges f ∈ ModCycleEdgeSets 5 G := by
  apply Basics.mem_modCycleEdgeSets_iff.mpr
  refine ⟨f 0, pentagonWalk G f hf.2.1 hf.2.2.1 hf.2.2.2.1
    hf.2.2.2.2.1 hf.2.2.2.2.2,
    pentagonWalk_isCycle G f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1
      hf.2.2.2.2.1 hf.2.2.2.2.2,
    pentagonWalk_edges G f hf.2.1 hf.2.2.1 hf.2.2.2.1
      hf.2.2.2.2.1 hf.2.2.2.2.2, ?_⟩
  exact dvd_refl 5

def cycleFiveVertices {v : V} (p : G.Walk v v) : Fin 5 → V :=
  fun i => p.getVert i.val

theorem cycleFiveVertices_injective {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hl : p.length = 5) :
    Function.Injective (cycleFiveVertices p) := by
  intro i j he
  apply Fin.ext
  exact hp.getVert_injOn'
    (by change i.val ≤ p.length - 1; omega)
    (by change j.val ≤ p.length - 1; omega) he

theorem cycleFiveVertices_isPentagon {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hl : p.length = 5) :
    IsPentagon G (cycleFiveVertices p) := by
  have h5 : p.getVert 5 = v := by simpa only [hl] using p.getVert_length
  refine ⟨cycleFiveVertices_injective hp hl, ?_, ?_, ?_, ?_, ?_⟩
  · exact p.adj_getVert_succ (i := 0) (by omega)
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · exact p.adj_getVert_succ (i := 2) (by omega)
  · exact p.adj_getVert_succ (i := 3) (by omega)
  · change G.Adj (p.getVert 4) (p.getVert 0)
    have ha := p.adj_getVert_succ (i := 4) (by omega : 4 < p.length)
    change G.Adj (p.getVert 4) (p.getVert 5) at ha
    simpa only [h5, Walk.getVert_zero] using ha

theorem five_edges_eq_getVert_list {v : V} {p : G.Walk v v}
    (hl : p.length = 5) :
    p.edges = [s(p.getVert 0, p.getVert 1), s(p.getVert 1, p.getVert 2),
      s(p.getVert 2, p.getVert 3), s(p.getVert 3, p.getVert 4),
      s(p.getVert 4, p.getVert 5)] := by
  apply List.ext_getElem
  · simp only [Walk.length_edges, hl, List.length_cons, List.length_nil]
  · intro i hi _
    rw [Walk.getElem_edges hi]
    have hi5 : i < 5 := by simpa only [Walk.length_edges, hl] using hi
    interval_cases i <;> rfl

theorem cycleFiveVertices_pentagonEdges [DecidableEq V] {v : V}
    {p : G.Walk v v} (hl : p.length = 5) :
    pentagonEdges (cycleFiveVertices p) = p.edges.toFinset := by
  have h5 : p.getVert 5 = v := by simpa only [hl] using p.getVert_length
  rw [five_edges_eq_getVert_list hl]
  simp [pentagonEdges, cycleFiveVertices, h5]

theorem exists_pentagon_of_cycle_length_five [DecidableEq V] {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hl : p.length = 5) :
    ∃ f : Fin 5 → V, IsPentagon G f ∧ pentagonEdges f = p.edges.toFinset :=
  ⟨cycleFiveVertices p, cycleFiveVertices_isPentagon hp hl,
    cycleFiveVertices_pentagonEdges hl⟩

theorem cycleContains_pentagonEdges_iff [DecidableEq V] (f : Fin 5 → V) (v : V) :
    CycleContains (pentagonEdges f) v ↔ ∃ i : Fin 5, f i = v := by
  constructor
  · rintro ⟨e, he, hv⟩
    simp only [pentagonEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
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
      · exact ⟨0, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [CycleContains, pentagonEdges]

theorem cycleVertices_pentagonEdges [Fintype V] [DecidableEq V]
    (f : Fin 5 → V) :
    TaskH.cycleVertices (pentagonEdges f) = Finset.univ.image f := by
  classical
  ext v
  simp only [TaskH.mem_cycleVertices, Finset.mem_image, Finset.mem_univ, true_and]
  exact cycleContains_pentagonEdges_iff f v

theorem cycleVertices_card_five_of_mem [Fintype V] (hs : ShortFiveCycles G)
    {s : Finset (Sym2 V)} (hmem : s ∈ ModCycleEdgeSets 5 G) :
    (TaskH.cycleVertices s).card = 5 := by
  classical
  obtain ⟨x, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  have hl := hs p hp hk
  obtain ⟨f, hf, hfe⟩ := exists_pentagon_of_cycle_length_five hp hl
  rw [← he, ← hfe, cycleVertices_pentagonEdges,
    Finset.card_image_of_injective _ hf.1, Finset.card_univ, Fintype.card_fin]

end TaskH.Five

#print axioms TaskH.Five.pentagonWalk_isCycle
#print axioms TaskH.Five.pentagonWalk_length
#print axioms TaskH.Five.pentagonWalk_edges
#print axioms TaskH.Five.pentagonEdges_mem_modCycleEdgeSets
#print axioms TaskH.Five.cycleFiveVertices_injective
#print axioms TaskH.Five.cycleFiveVertices_isPentagon
#print axioms TaskH.Five.five_edges_eq_getVert_list
#print axioms TaskH.Five.cycleFiveVertices_pentagonEdges
#print axioms TaskH.Five.exists_pentagon_of_cycle_length_five
#print axioms TaskH.Five.cycleContains_pentagonEdges_iff
#print axioms TaskH.Five.cycleVertices_pentagonEdges
#print axioms TaskH.Five.cycleVertices_card_five_of_mem
