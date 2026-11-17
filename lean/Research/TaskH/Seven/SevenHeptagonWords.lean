import Research.TaskH.Seven.SevenHeptagonWordIndices

/-!
Actual ordered heptagons and their fourteen-word undirected edge-set fibers.
Neither ShortSevenCycles nor a cycle-count equality is assumed here.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem heptagonWord_adj_succ {f : Fin 7 → V} (hf : IsHeptagon G f) (i : Fin 7) :
    G.Adj (f i) (f (i + 1)) := by
  fin_cases i
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2.1
  · exact hf.2.2.2.2.1
  · exact hf.2.2.2.2.2.1
  · exact hf.2.2.2.2.2.2.1
  · exact hf.2.2.2.2.2.2.2

theorem heptagonWord_adj_of_indexAdj {f : Fin 7 → V} (hf : IsHeptagon G f)
    {a b : Fin 7} (hab : HeptagonIndexAdj a b) : G.Adj (f a) (f b) := by
  rcases hab with rfl | rfl
  · exact heptagonWord_adj_succ hf a
  · have hh := (heptagonWord_adj_succ hf (a - 1)).symm
    simpa only [sub_add_cancel] using hh

theorem heptagonEdges_comp [DecidableEq V] (f : Fin 7 → V) (σ : Fin 7 → Fin 7) :
    heptagonEdges (f ∘ σ) = (heptagonEdges σ).image (Sym2.map f) := by
  simp [heptagonEdges]

theorem heptagonEdges_eq_image_indexEdges [DecidableEq V] (f : Fin 7 → V) :
    heptagonEdges f =
      (heptagonEdges (id : Fin 7 → Fin 7)).image (Sym2.map f) := by
  simpa only [Function.comp_id] using heptagonEdges_comp f id

theorem heptagonEdges_index_mem_iff [DecidableEq V] (f : Fin 7 → V)
    (hf : Function.Injective f) (a b : Fin 7) :
    s(f a, f b) ∈ heptagonEdges f ↔ HeptagonIndexAdj a b := by
  rw [heptagonEdges_eq_image_indexEdges]
  constructor
  · intro h
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    have he' : e = s(a, b) := (Sym2.map.injective hf) (by simpa using heq)
    rw [he'] at he
    exact (heptagon_index_edge_iff a b).mp he
  · intro h
    exact Finset.mem_image.mpr ⟨s(a, b), (heptagon_index_edge_iff a b).mpr h, rfl⟩

theorem heptagon_step_edge_mem [DecidableEq V] (f : Fin 7 → V) (i : Fin 7) :
    s(f i, f (i + 1)) ∈ heptagonEdges f := by
  fin_cases i <;> simp [heptagonEdges]

theorem isHeptagon_reindex (f : Fin 7 → V) (hf : IsHeptagon G f)
    (o : Bool × Fin 7) : IsHeptagon G (f ∘ heptagonOrientedIndex o.1 o.2) := by
  refine ⟨hf.1.comp (heptagonOrientedIndex_injective o.1 o.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact heptagonWord_adj_of_indexAdj hf (heptagonOrientedIndex_adj o.1 o.2 0)
  · exact heptagonWord_adj_of_indexAdj hf (heptagonOrientedIndex_adj o.1 o.2 1)
  · exact heptagonWord_adj_of_indexAdj hf (heptagonOrientedIndex_adj o.1 o.2 2)
  · exact heptagonWord_adj_of_indexAdj hf (heptagonOrientedIndex_adj o.1 o.2 3)
  · exact heptagonWord_adj_of_indexAdj hf (heptagonOrientedIndex_adj o.1 o.2 4)
  · exact heptagonWord_adj_of_indexAdj hf (heptagonOrientedIndex_adj o.1 o.2 5)
  · exact heptagonWord_adj_of_indexAdj hf (heptagonOrientedIndex_adj o.1 o.2 6)

theorem heptagonEdges_reindex [DecidableEq V] (f : Fin 7 → V) (o : Bool × Fin 7) :
    heptagonEdges (f ∘ heptagonOrientedIndex o.1 o.2) = heptagonEdges f := by
  rw [heptagonEdges_comp, heptagonOrientedIndex_edges, ← heptagonEdges_eq_image_indexEdges]

theorem heptagon_reindex_parameters_injective (f : Fin 7 → V)
    (hf : Function.Injective f) :
    Function.Injective (fun o : Bool × Fin 7 => f ∘ heptagonOrientedIndex o.1 o.2) := by
  intro o p he
  apply heptagonOrientedIndex_parameters_injective
  funext i
  apply hf
  exact congrFun he i

theorem heptagon_same_edges_reindex [DecidableEq V]
    (f g : Fin 7 → V) (hf : IsHeptagon G f) (hg : IsHeptagon G g)
    (he : heptagonEdges g = heptagonEdges f) :
    ∃ o : Bool × Fin 7, g = f ∘ heptagonOrientedIndex o.1 o.2 := by
  classical
  have hpre : ∀ i : Fin 7, ∃ j : Fin 7, f j = g i := by
    intro i
    apply (cycleContains_heptagonEdges_iff f (g i)).mp
    rw [← he]
    exact (cycleContains_heptagonEdges_iff g (g i)).mpr ⟨i, rfl⟩
  let σ : Fin 7 → Fin 7 := fun i => Classical.choose (hpre i)
  have hσf : ∀ i, f (σ i) = g i := fun i => Classical.choose_spec (hpre i)
  have hσ : Function.Injective σ := by
    intro i j hij
    apply hg.1
    rw [← hσf i, ← hσf j, hij]
  have hstep : ∀ i, HeptagonIndexAdj (σ i) (σ (i + 1)) := by
    intro i
    apply (heptagonEdges_index_mem_iff f hf.1 _ _).mp
    rw [hσf i, hσf (i + 1), ← he]
    exact heptagon_step_edge_mem g i
  obtain ⟨o, ho⟩ := heptagon_index_word_dihedral σ hσ hstep
  refine ⟨o, ?_⟩
  funext i
  simpa only [Function.comp_apply, ← ho] using (hσf i).symm

noncomputable def heptagonWords [Fintype V] (G : SimpleGraph V) :
    Finset (Fin 7 → V) := by
  classical
  exact Finset.univ.filter (IsHeptagon G)

noncomputable def actualSevenEdgeSets [Fintype V] (G : SimpleGraph V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (heptagonWords G).image heptagonEdges

theorem mem_heptagonWords_iff [Fintype V] (f : Fin 7 → V) :
    f ∈ heptagonWords G ↔ IsHeptagon G f := by
  classical
  simp [heptagonWords]

open scoped Classical in
theorem mem_actualSevenEdgeSets_iff [Fintype V] (s : Finset (Sym2 V)) :
    s ∈ actualSevenEdgeSets G ↔ ∃ f : Fin 7 → V, IsHeptagon G f ∧ heptagonEdges f = s := by
  classical
  simp [actualSevenEdgeSets, mem_heptagonWords_iff]

end TaskH.Seven

#print axioms TaskH.Seven.heptagonWord_adj_succ
#print axioms TaskH.Seven.heptagonWord_adj_of_indexAdj
#print axioms TaskH.Seven.heptagonEdges_comp
#print axioms TaskH.Seven.heptagonEdges_eq_image_indexEdges
#print axioms TaskH.Seven.heptagonEdges_index_mem_iff
#print axioms TaskH.Seven.heptagon_step_edge_mem
#print axioms TaskH.Seven.isHeptagon_reindex
#print axioms TaskH.Seven.heptagonEdges_reindex
#print axioms TaskH.Seven.heptagon_reindex_parameters_injective
#print axioms TaskH.Seven.heptagon_same_edges_reindex
#print axioms TaskH.Seven.heptagonWords
#print axioms TaskH.Seven.actualSevenEdgeSets
#print axioms TaskH.Seven.mem_heptagonWords_iff
#print axioms TaskH.Seven.mem_actualSevenEdgeSets_iff
