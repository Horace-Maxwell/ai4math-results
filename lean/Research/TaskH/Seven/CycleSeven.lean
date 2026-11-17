import Research.TaskH.Seven.Definitions

/-! Seven original vertices encode a true cycle and its unoriented edge set. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

def heptagonEdges [DecidableEq V] (f : Fin 7 → V) : Finset (Sym2 V) :=
  {s(f 0, f 1), s(f 1, f 2), s(f 2, f 3), s(f 3, f 4), s(f 4, f 5), s(f 5, f 6), s(f 6, f 0)}

def IsHeptagon (G : SimpleGraph V) (f : Fin 7 → V) : Prop :=
  Function.Injective f ∧ G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧ G.Adj (f 2) (f 3) ∧ G.Adj (f 3) (f 4) ∧ G.Adj (f 4) (f 5) ∧ G.Adj (f 5) (f 6) ∧ G.Adj (f 6) (f 0)

def heptagonWalk (G : SimpleGraph V) (f : Fin 7 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h45 : G.Adj (f 4) (f 5)) (h56 : G.Adj (f 5) (f 6))
    (h60 : G.Adj (f 6) (f 0)) : G.Walk (f 0) (f 0) :=
  .cons h01 (.cons h12 (.cons h23 (.cons h34 (.cons h45 (.cons h56 (.cons h60 .nil))))))

theorem heptagonWalk_isCycle (G : SimpleGraph V) (f : Fin 7 → V)
    (hf : Function.Injective f)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h45 : G.Adj (f 4) (f 5)) (h56 : G.Adj (f 5) (f 6))
    (h60 : G.Adj (f 6) (f 0)) :
    (heptagonWalk G f h01 h12 h23 h34 h45 h56 h60).IsCycle := by
  rw [heptagonWalk, Walk.cons_isCycle_iff]
  constructor
  · apply Walk.IsPath.mk'
    simp [Walk.support_cons, hf.eq_iff]
  · simp [Walk.edges_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
      Prod.swap_prod_mk, hf.eq_iff]

theorem heptagonWalk_length (G : SimpleGraph V) (f : Fin 7 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h45 : G.Adj (f 4) (f 5)) (h56 : G.Adj (f 5) (f 6))
    (h60 : G.Adj (f 6) (f 0)) :
    (heptagonWalk G f h01 h12 h23 h34 h45 h56 h60).length = 7 := rfl

theorem heptagonWalk_edges [DecidableEq V] (G : SimpleGraph V) (f : Fin 7 → V)
    (h01 : G.Adj (f 0) (f 1)) (h12 : G.Adj (f 1) (f 2))
    (h23 : G.Adj (f 2) (f 3)) (h34 : G.Adj (f 3) (f 4))
    (h45 : G.Adj (f 4) (f 5)) (h56 : G.Adj (f 5) (f 6))
    (h60 : G.Adj (f 6) (f 0)) :
    (heptagonWalk G f h01 h12 h23 h34 h45 h56 h60).edges.toFinset = heptagonEdges f := by
  simp [heptagonWalk, heptagonEdges, Walk.edges_cons]

theorem heptagonEdges_mem_modCycleEdgeSets [DecidableEq V]
    (f : Fin 7 → V) (hf : IsHeptagon G f) :
    heptagonEdges f ∈ ModCycleEdgeSets 7 G := by
  rcases hf with ⟨hinj, h01, h12, h23, h34, h45, h56, h60⟩
  apply Basics.mem_modCycleEdgeSets_iff.mpr
  refine ⟨f 0, heptagonWalk G f h01 h12 h23 h34 h45 h56 h60,
    heptagonWalk_isCycle G f hinj h01 h12 h23 h34 h45 h56 h60,
    heptagonWalk_edges G f h01 h12 h23 h34 h45 h56 h60, ?_⟩
  exact dvd_refl 7

def cycleSevenVertices {v : V} (p : G.Walk v v) : Fin 7 → V :=
  fun i => p.getVert i.val

theorem cycleSevenVertices_injective {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hl : p.length = 7) :
    Function.Injective (cycleSevenVertices p) := by
  intro i j he
  apply Fin.ext
  exact hp.getVert_injOn'
    (by change i.val ≤ p.length - 1; omega)
    (by change j.val ≤ p.length - 1; omega) he

theorem cycleSevenVertices_isHeptagon {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) (hl : p.length = 7) :
    IsHeptagon G (cycleSevenVertices p) := by
  have h7 : p.getVert 7 = v := by simpa only [hl] using p.getVert_length
  refine ⟨cycleSevenVertices_injective hp hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact p.adj_getVert_succ (i := 0) (by omega)
  · exact p.adj_getVert_succ (i := 1) (by omega)
  · exact p.adj_getVert_succ (i := 2) (by omega)
  · exact p.adj_getVert_succ (i := 3) (by omega)
  · exact p.adj_getVert_succ (i := 4) (by omega)
  · exact p.adj_getVert_succ (i := 5) (by omega)
  · change G.Adj (p.getVert 6) (p.getVert 0)
    have ha := p.adj_getVert_succ (i := 6) (by omega : 6 < p.length)
    change G.Adj (p.getVert 6) (p.getVert 7) at ha
    simpa only [h7, Walk.getVert_zero] using ha

theorem seven_edges_eq_getVert_list {v : V} {p : G.Walk v v}
    (hl : p.length = 7) :
    p.edges = [s(p.getVert 0, p.getVert 1),
      s(p.getVert 1, p.getVert 2),
      s(p.getVert 2, p.getVert 3),
      s(p.getVert 3, p.getVert 4),
      s(p.getVert 4, p.getVert 5),
      s(p.getVert 5, p.getVert 6),
      s(p.getVert 6, p.getVert 7)] := by
  apply List.ext_getElem
  · simp only [Walk.length_edges, hl, List.length_cons, List.length_nil]
  · intro i hi _
    rw [Walk.getElem_edges hi]
    have hi7 : i < 7 := by simpa only [Walk.length_edges, hl] using hi
    interval_cases i <;> rfl

theorem cycleSevenVertices_heptagonEdges [DecidableEq V] {v : V}
    {p : G.Walk v v} (hl : p.length = 7) :
    heptagonEdges (cycleSevenVertices p) = p.edges.toFinset := by
  have h7 : p.getVert 7 = v := by simpa only [hl] using p.getVert_length
  rw [seven_edges_eq_getVert_list hl]
  simp [heptagonEdges, cycleSevenVertices, h7]

theorem exists_heptagon_of_cycle_length_seven [DecidableEq V] {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hl : p.length = 7) :
    ∃ f : Fin 7 → V, IsHeptagon G f ∧ heptagonEdges f = p.edges.toFinset :=
  ⟨cycleSevenVertices p, cycleSevenVertices_isHeptagon hp hl,
    cycleSevenVertices_heptagonEdges hl⟩

theorem cycleContains_heptagonEdges_iff [DecidableEq V] (f : Fin 7 → V) (v : V) :
    CycleContains (heptagonEdges f) v ↔ ∃ i : Fin 7, f i = v := by
  constructor
  · rintro ⟨e, he, hv⟩
    simp only [heptagonEdges, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · exact ⟨6, h.symm⟩
    · rcases hv with h | h
      · exact ⟨6, h.symm⟩
      · exact ⟨0, h.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [CycleContains, heptagonEdges]

theorem cycleVertices_heptagonEdges [Fintype V] [DecidableEq V]
    (f : Fin 7 → V) :
    TaskH.cycleVertices (heptagonEdges f) = Finset.univ.image f := by
  classical
  ext v
  simp only [TaskH.mem_cycleVertices, Finset.mem_image, Finset.mem_univ, true_and]
  exact cycleContains_heptagonEdges_iff f v

theorem cycleVertices_card_seven_of_mem [Fintype V] (hs : ShortSevenCycles G)
    {s : Finset (Sym2 V)} (hmem : s ∈ ModCycleEdgeSets 7 G) :
    (TaskH.cycleVertices s).card = 7 := by
  classical
  obtain ⟨x, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  have hl := hs p hp hk
  obtain ⟨f, hf, hfe⟩ := exists_heptagon_of_cycle_length_seven hp hl
  rw [← he, ← hfe, cycleVertices_heptagonEdges,
    Finset.card_image_of_injective _ hf.1, Finset.card_univ, Fintype.card_fin]

end TaskH.Seven

#print axioms TaskH.Seven.heptagonEdges
#print axioms TaskH.Seven.IsHeptagon
#print axioms TaskH.Seven.heptagonWalk
#print axioms TaskH.Seven.heptagonWalk_isCycle
#print axioms TaskH.Seven.heptagonWalk_length
#print axioms TaskH.Seven.heptagonWalk_edges
#print axioms TaskH.Seven.heptagonEdges_mem_modCycleEdgeSets
#print axioms TaskH.Seven.cycleSevenVertices
#print axioms TaskH.Seven.cycleSevenVertices_injective
#print axioms TaskH.Seven.cycleSevenVertices_isHeptagon
#print axioms TaskH.Seven.seven_edges_eq_getVert_list
#print axioms TaskH.Seven.cycleSevenVertices_heptagonEdges
#print axioms TaskH.Seven.exists_heptagon_of_cycle_length_seven
#print axioms TaskH.Seven.cycleContains_heptagonEdges_iff
#print axioms TaskH.Seven.cycleVertices_heptagonEdges
#print axioms TaskH.Seven.cycleVertices_card_seven_of_mem
