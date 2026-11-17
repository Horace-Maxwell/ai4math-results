import Research.TaskH.Five.FiveLightEdgeOutside

/-! Transport finite chord masks and gem hooks into the actual graph. -/

universe u

namespace TaskH.Five

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

noncomputable def lightActualChords (G : SimpleGraph V) (f : Fin 5 → V) :
    Finset (Fin 5) := by
  classical
  exact Finset.univ.filter (fun i =>
    G.Adj (f (lightChordEnds i).1) (f (lightChordEnds i).2))

theorem light_indices_cycle_or_chord (i j : Fin 5) (hne : i ≠ j) :
    s(i, j) ∈ lightCycleIndices ∨ ∃ k : Fin 5, lightChord k = s(i, j) := by
  revert i j
  decide +kernel

theorem light_cycle_edge_actual {f : Fin 5 → V} (hf : IsPentagon G f)
    (i j : Fin 5) (h : s(i, j) ∈ lightCycleIndices) : G.Adj (f i) (f j) := by
  simp only [lightCycleIndices, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h | h
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf.2.1
    · exact hf.2.1.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf.2.2.1
    · exact hf.2.2.1.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf.2.2.2.1
    · exact hf.2.2.2.1.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf.2.2.2.2.1
    · exact hf.2.2.2.2.1.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf.2.2.2.2.2
    · exact hf.2.2.2.2.2.symm

theorem light_index_edges_actual_iff {f : Fin 5 → V} (hf : IsPentagon G f)
    (i j : Fin 5) :
    s(i, j) ∈ lightIndexEdges (lightActualChords G f) ↔ G.Adj (f i) (f j) := by
  classical
  constructor
  · intro hij
    rcases Finset.mem_union.mp hij with hcycle | hchord
    · exact light_cycle_edge_actual hf i j hcycle
    · obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hchord
      simp only [lightActualChords, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have he : s((lightChordEnds k).1, (lightChordEnds k).2) = s(i, j) := heq
      rcases Sym2.eq_iff.mp he with ⟨hki, hkj⟩ | ⟨hkj, hki⟩
      · rw [← hki, ← hkj]
        exact hk
      · rw [← hki, ← hkj]
        exact hk.symm
  · intro hij
    have hne : i ≠ j := fun he => hij.ne (congrArg f he)
    rcases light_indices_cycle_or_chord i j hne with hcycle | ⟨k, hk⟩
    · exact Finset.mem_union.mpr (Or.inl hcycle)
    · have he : s((lightChordEnds k).1, (lightChordEnds k).2) = s(i, j) := hk
      have ha : G.Adj (f (lightChordEnds k).1) (f (lightChordEnds k).2) := by
        rcases Sym2.eq_iff.mp he with ⟨hki, hkj⟩ | ⟨hkj, hki⟩
        · rw [hki, hkj]
          exact hij
        · rw [hki, hkj]
          exact hij.symm
      have hkmem : k ∈ lightActualChords G f := by
        simp only [lightActualChords, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ha
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨k, hkmem, hk⟩))

theorem light_gem_embedding_of_edges (r : Fin 5 → V) (hr : Function.Injective r)
    (h01 : G.Adj (r 0) (r 1)) (h12 : G.Adj (r 1) (r 2))
    (h23 : G.Adj (r 2) (r 3)) (h04 : G.Adj (r 0) (r 4))
    (h14 : G.Adj (r 1) (r 4)) (h24 : G.Adj (r 2) (r 4))
    (h34 : G.Adj (r 3) (r 4)) : PatternEmbedding G patternGem r := by
  refine ⟨hr, ?_⟩
  intro i j hij
  simp only [patternGem, Finset.mem_insert, Finset.mem_singleton] at hij
  rcases hij with h | h | h | h | h | h | h
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h01
    · exact h01.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h12
    · exact h12.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h23
    · exact h23.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h04
    · exact h04.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h14
    · exact h14.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h24
    · exact h24.symm
  · rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h34
    · exact h34.symm

theorem light_index_gem_embedding {f : Fin 5 → V} (hf : IsPentagon G f)
    (g : Equiv.Perm (Fin 5))
    (hg : LightIndexGem (lightIndexEdges (lightActualChords G f)) g) :
    PatternEmbedding G patternGem (f ∘ g) := by
  rcases hg with ⟨h01, h12, h23, h04, h14, h24, h34⟩
  exact light_gem_embedding_of_edges (f ∘ g) (hf.1.comp g.injective)
    ((light_index_edges_actual_iff hf _ _).mp h01)
    ((light_index_edges_actual_iff hf _ _).mp h12)
    ((light_index_edges_actual_iff hf _ _).mp h23)
    ((light_index_edges_actual_iff hf _ _).mp h04)
    ((light_index_edges_actual_iff hf _ _).mp h14)
    ((light_index_edges_actual_iff hf _ _).mp h24)
    ((light_index_edges_actual_iff hf _ _).mp h34)

def lightGemOutsideVertices (f : Fin 5 → V) (a b u v : Fin 5) (w : V) :
    Fin 5 → V := ![f a, f b, f u, w, f v]

theorem lightGemOutsideVertices_injective (f : Fin 5 → V)
    (hf : Function.Injective f) (a b u v : Fin 5) (w : V)
    (hfour : Function.Injective (![a, b, u, v] : Fin 4 → Fin 5))
    (hw : ∀ j : Fin 5, w ≠ f j) :
    Function.Injective (lightGemOutsideVertices f a b u v w) := by
  have hab : a ≠ b := hfour.ne (by decide : (0 : Fin 4) ≠ 1)
  have hau : a ≠ u := hfour.ne (by decide : (0 : Fin 4) ≠ 2)
  have hav : a ≠ v := hfour.ne (by decide : (0 : Fin 4) ≠ 3)
  have hbu : b ≠ u := hfour.ne (by decide : (1 : Fin 4) ≠ 2)
  have hbv : b ≠ v := hfour.ne (by decide : (1 : Fin 4) ≠ 3)
  have huv : u ≠ v := hfour.ne (by decide : (2 : Fin 4) ≠ 3)
  have hfw : ∀ j : Fin 5, f j ≠ w := fun j => (hw j).symm
  intro i j he
  fin_cases i <;> fin_cases j <;>
    simp_all [lightGemOutsideVertices, hf.eq_iff, ne_comm]
  · exact hw a he.symm
  · exact hw b he.symm
  · exact hw u he.symm
  · exact hw v he.symm

theorem light_hook_forbids_outside_common {f : Fin 5 → V} (hf : IsPentagon G f)
    (hgem : ∀ r : Fin 5 → V, ¬ PatternEmbedding G patternGem r)
    (u v : Fin 5)
    (hh : LightGemHook (lightIndexEdges (lightActualChords G f)) u v)
    (w : V) (hu : G.Adj (f u) w) (hv : G.Adj (f v) w) :
    ∃ j : Fin 5, f j = w := by
  classical
  by_contra hout
  have hw : ∀ j : Fin 5, w ≠ f j := by
    intro j he
    exact hout ⟨j, he.symm⟩
  obtain ⟨a, b, hinj, hab, hbu, hva, hvb, hvu⟩ := hh
  let r := lightGemOutsideVertices f a b u v w
  apply hgem r
  exact light_gem_embedding_of_edges r
    (lightGemOutsideVertices_injective f hf.1 a b u v w hinj hw)
    ((light_index_edges_actual_iff hf a b).mp hab)
    ((light_index_edges_actual_iff hf b u).mp hbu) hu
    (((light_index_edges_actual_iff hf v a).mp hva).symm)
    (((light_index_edges_actual_iff hf v b).mp hvb).symm)
    (((light_index_edges_actual_iff hf v u).mp hvu).symm) hv.symm

theorem light_common_card_bound {f : Fin 5 → V} (hf : IsPentagon G f)
    (u v : Fin 5)
    (hout : ∀ w : V, G.Adj (f u) w → G.Adj (f v) w →
      ∃ j : Fin 5, f j = w)
    (hcard : (lightIndexCommon (lightIndexEdges (lightActualChords G f)) u v).card ≤ 1) :
    (G.commonNeighbors (f u) (f v)).ncard ≤ 1 := by
  classical
  let I := lightIndexCommon (lightIndexEdges (lightActualChords G f)) u v
  have he : G.commonNeighbors (f u) (f v) = (I.image f : Set V) := by
    ext w
    simp only [G.mem_commonNeighbors, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨huw, hvw⟩
      obtain ⟨j, rfl⟩ := hout w huw hvw
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      exact ⟨(light_index_edges_actual_iff hf u j).mpr huw,
        (light_index_edges_actual_iff hf v j).mpr hvw⟩
    · rintro ⟨j, hj, rfl⟩
      have hp := (Finset.mem_filter.mp hj).2
      exact ⟨(light_index_edges_actual_iff hf u j).mp hp.1,
        (light_index_edges_actual_iff hf v j).mp hp.2⟩
  rw [he, Set.ncard_coe_finset]
  exact (Finset.card_image_le).trans hcard

end TaskH.Five

#print axioms TaskH.Five.lightActualChords
#print axioms TaskH.Five.light_indices_cycle_or_chord
#print axioms TaskH.Five.light_cycle_edge_actual
#print axioms TaskH.Five.light_index_edges_actual_iff
#print axioms TaskH.Five.light_gem_embedding_of_edges
#print axioms TaskH.Five.light_index_gem_embedding
#print axioms TaskH.Five.lightGemOutsideVertices
#print axioms TaskH.Five.lightGemOutsideVertices_injective
#print axioms TaskH.Five.light_hook_forbids_outside_common
#print axioms TaskH.Five.light_common_card_bound
