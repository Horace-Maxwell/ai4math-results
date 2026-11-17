import Research.TaskH.Six.HexagonWordIndices

/-!
Actual ordered hexagons and their twelve-word undirected edge-set fibers.
Neither ShortSixCycles nor a cycle-count equality is assumed here.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem hexagon_adj_succ {f : Fin 6 → V} (hf : IsHexagon G f) (i : Fin 6) :
    G.Adj (f i) (f (i + 1)) := by
  fin_cases i
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2.1
  · exact hf.2.2.2.2.1
  · exact hf.2.2.2.2.2.1
  · exact hf.2.2.2.2.2.2

theorem hexagon_adj_of_indexAdj {f : Fin 6 → V} (hf : IsHexagon G f)
    {a b : Fin 6} (hab : HexagonIndexAdj a b) : G.Adj (f a) (f b) := by
  rcases hab with rfl | rfl
  · exact hexagon_adj_succ hf a
  · have hh := (hexagon_adj_succ hf (a - 1)).symm
    simpa only [sub_add_cancel] using hh

theorem hexagonEdges_comp [DecidableEq V] (f : Fin 6 → V) (σ : Fin 6 → Fin 6) :
    hexagonEdges (f ∘ σ) = (hexagonEdges σ).image (Sym2.map f) := by
  simp [hexagonEdges]

theorem hexagonEdges_eq_image_indexEdges [DecidableEq V] (f : Fin 6 → V) :
    hexagonEdges f =
      (hexagonEdges (id : Fin 6 → Fin 6)).image (Sym2.map f) := by
  simpa only [Function.comp_id] using hexagonEdges_comp f id

theorem hexagonEdges_index_mem_iff [DecidableEq V] (f : Fin 6 → V)
    (hf : Function.Injective f) (a b : Fin 6) :
    s(f a, f b) ∈ hexagonEdges f ↔ HexagonIndexAdj a b := by
  rw [hexagonEdges_eq_image_indexEdges]
  constructor
  · intro h
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    have he' : e = s(a, b) := (Sym2.map.injective hf) (by simpa using heq)
    rw [he'] at he
    exact (hexagon_index_edge_iff a b).mp he
  · intro h
    exact Finset.mem_image.mpr ⟨s(a, b), (hexagon_index_edge_iff a b).mpr h, rfl⟩

theorem hexagon_step_edge_mem [DecidableEq V] (f : Fin 6 → V) (i : Fin 6) :
    s(f i, f (i + 1)) ∈ hexagonEdges f := by
  fin_cases i <;> simp [hexagonEdges]

theorem isHexagon_reindex (f : Fin 6 → V) (hf : IsHexagon G f)
    (o : Bool × Fin 6) : IsHexagon G (f ∘ hexagonOrientedIndex o.1 o.2) := by
  refine ⟨hf.1.comp (hexagonOrientedIndex_injective o.1 o.2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hexagon_adj_of_indexAdj hf (hexagonOrientedIndex_adj o.1 o.2 0)
  · exact hexagon_adj_of_indexAdj hf (hexagonOrientedIndex_adj o.1 o.2 1)
  · exact hexagon_adj_of_indexAdj hf (hexagonOrientedIndex_adj o.1 o.2 2)
  · exact hexagon_adj_of_indexAdj hf (hexagonOrientedIndex_adj o.1 o.2 3)
  · exact hexagon_adj_of_indexAdj hf (hexagonOrientedIndex_adj o.1 o.2 4)
  · exact hexagon_adj_of_indexAdj hf (hexagonOrientedIndex_adj o.1 o.2 5)

theorem hexagonEdges_reindex [DecidableEq V] (f : Fin 6 → V) (o : Bool × Fin 6) :
    hexagonEdges (f ∘ hexagonOrientedIndex o.1 o.2) = hexagonEdges f := by
  rw [hexagonEdges_comp, hexagonOrientedIndex_edges, ← hexagonEdges_eq_image_indexEdges]

theorem hexagon_reindex_parameters_injective (f : Fin 6 → V)
    (hf : Function.Injective f) :
    Function.Injective (fun o : Bool × Fin 6 => f ∘ hexagonOrientedIndex o.1 o.2) := by
  intro o p he
  apply hexagonOrientedIndex_parameters_injective
  funext i
  apply hf
  exact congrFun he i

theorem hexagon_same_edges_reindex [DecidableEq V]
    (f g : Fin 6 → V) (hf : IsHexagon G f) (hg : IsHexagon G g)
    (he : hexagonEdges g = hexagonEdges f) :
    ∃ o : Bool × Fin 6, g = f ∘ hexagonOrientedIndex o.1 o.2 := by
  classical
  have hpre : ∀ i : Fin 6, ∃ j : Fin 6, f j = g i := by
    intro i
    apply (cycleContains_hexagonEdges_iff f (g i)).mp
    rw [← he]
    exact (cycleContains_hexagonEdges_iff g (g i)).mpr ⟨i, rfl⟩
  let σ : Fin 6 → Fin 6 := fun i => Classical.choose (hpre i)
  have hσf : ∀ i, f (σ i) = g i := fun i => Classical.choose_spec (hpre i)
  have hσ : Function.Injective σ := by
    intro i j hij
    apply hg.1
    rw [← hσf i, ← hσf j, hij]
  have hstep : ∀ i, HexagonIndexAdj (σ i) (σ (i + 1)) := by
    intro i
    apply (hexagonEdges_index_mem_iff f hf.1 _ _).mp
    rw [hσf i, hσf (i + 1), ← he]
    exact hexagon_step_edge_mem g i
  obtain ⟨o, ho⟩ := hexagon_index_word_dihedral σ hσ hstep
  refine ⟨o, ?_⟩
  funext i
  simpa only [Function.comp_apply, ← ho] using (hσf i).symm

noncomputable def hexagonWords [Fintype V] (G : SimpleGraph V) :
    Finset (Fin 6 → V) := by
  classical
  exact Finset.univ.filter (IsHexagon G)

noncomputable def actualSixEdgeSets [Fintype V] (G : SimpleGraph V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (hexagonWords G).image hexagonEdges

theorem mem_hexagonWords_iff [Fintype V] (f : Fin 6 → V) :
    f ∈ hexagonWords G ↔ IsHexagon G f := by
  classical
  simp [hexagonWords]

open scoped Classical in
theorem mem_actualSixEdgeSets_iff [Fintype V] (s : Finset (Sym2 V)) :
    s ∈ actualSixEdgeSets G ↔ ∃ f : Fin 6 → V, IsHexagon G f ∧ hexagonEdges f = s := by
  classical
  simp [actualSixEdgeSets, mem_hexagonWords_iff]

end TaskH.Six

#print axioms TaskH.Six.hexagon_adj_succ
#print axioms TaskH.Six.hexagon_adj_of_indexAdj
#print axioms TaskH.Six.hexagonEdges_comp
#print axioms TaskH.Six.hexagonEdges_eq_image_indexEdges
#print axioms TaskH.Six.hexagonEdges_index_mem_iff
#print axioms TaskH.Six.hexagon_step_edge_mem
#print axioms TaskH.Six.isHexagon_reindex
#print axioms TaskH.Six.hexagonEdges_reindex
#print axioms TaskH.Six.hexagon_reindex_parameters_injective
#print axioms TaskH.Six.hexagon_same_edges_reindex
#print axioms TaskH.Six.hexagonWords
#print axioms TaskH.Six.actualSixEdgeSets
#print axioms TaskH.Six.mem_hexagonWords_iff
#print axioms TaskH.Six.mem_actualSixEdgeSets_iff
