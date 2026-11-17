import Research.TaskH.Five.FiveForcedGroupBudget

/-! The literal path tables force colors in each single deleted-vertex coloring. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

def GemLeftIndices (A : Finset (Fin 5)) : Prop :=
  A = {4, 1} ∨ A = {4, 3} ∨ A = {2, 3}

def GemRightIndices (A : Finset (Fin 5)) : Prop :=
  A = {4, 2} ∨ A = {4, 0} ∨ A = {0, 1}

theorem gem_left_right_disjoint (A : Finset (Fin 5))
    (hl : GemLeftIndices A) (hr : GemRightIndices A) : False := by
  unfold GemLeftIndices at hl
  unfold GemRightIndices at hr
  revert A
  decide +kernel

theorem gem_left_card_two (A : Finset (Fin 5)) (hl : GemLeftIndices A) : A.card = 2 := by
  unfold GemLeftIndices at hl
  revert A
  decide +kernel

theorem gem_right_card_two (A : Finset (Fin 5)) (hr : GemRightIndices A) : A.card = 2 := by
  unfold GemRightIndices at hr
  revert A
  decide +kernel

theorem star_double_neighbor_forced {f : Fin 5 → V}
    (hr : RainbowFiveCycles G) (hf : PatternEmbedding G patternStar f)
    (y : V) (hy : y ∉ patternVertexSet f)
    (hcard : (patternNeighborIndices G f y).card = 2) : ForcedTo G f 4 y := by
  intro w c hfw hyw
  have hyout : ∀ i, y ≠ f i := by
    intro i hi
    apply hy
    rw [hi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨q, hqcol, hqA, hno⟩ := pattern_coloring_attachment_constraints
    hr hf patternStar_hamilton w c hfw y hyw hyout
  have ht := star_attachment_table q (patternNeighborIndices G f y) hqA hcard hno
  simpa only [ht.1] using hqcol

theorem gem_left_neighbor_forced {f : Fin 5 → V}
    (hr : RainbowFiveCycles G) (hf : PatternEmbedding G patternGem f)
    (y : V) (hy : y ∉ patternVertexSet f)
    (hleft : GemLeftIndices (patternNeighborIndices G f y)) : ForcedTo G f 0 y := by
  intro w c hfw hyw
  have hyout : ∀ i, y ≠ f i := by
    intro i hi
    apply hy
    rw [hi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨q, hqcol, hqA, hno⟩ := pattern_coloring_attachment_constraints
    hr hf patternGem_hamilton w c hfw y hyw hyout
  have ht := gem_attachment_table q (patternNeighborIndices G f y) hqA
    (gem_left_card_two _ hleft) hno
  rcases ht with ⟨hq, _⟩ | ⟨_, hright⟩
  · simpa only [hq] using hqcol
  · exact False.elim (gem_left_right_disjoint _ hleft hright)

theorem gem_right_neighbor_forced {f : Fin 5 → V}
    (hr : RainbowFiveCycles G) (hf : PatternEmbedding G patternGem f)
    (y : V) (hy : y ∉ patternVertexSet f)
    (hright : GemRightIndices (patternNeighborIndices G f y)) : ForcedTo G f 3 y := by
  intro w c hfw hyw
  have hyout : ∀ i, y ≠ f i := by
    intro i hi
    apply hy
    rw [hi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨q, hqcol, hqA, hno⟩ := pattern_coloring_attachment_constraints
    hr hf patternGem_hamilton w c hfw y hyw hyout
  have ht := gem_attachment_table q (patternNeighborIndices G f y) hqA
    (gem_right_card_two _ hright) hno
  rcases ht with ⟨_, hleft⟩ | ⟨hq, _⟩
  · exact False.elim (gem_left_right_disjoint _ hleft hright)
  · simpa only [hq] using hqcol

variable [Fintype V]

noncomputable def doubleOuterVertices (G : SimpleGraph V) (f : Fin 5 → V) : Finset V :=
  (patternVertexSet f)ᶜ.filter (fun y => (patternNeighborIndices G f y).card = 2)

noncomputable def gemLeftVertices (G : SimpleGraph V) (f : Fin 5 → V) : Finset V :=
  (patternVertexSet f)ᶜ.filter (fun y => GemLeftIndices (patternNeighborIndices G f y))

noncomputable def gemRightVertices (G : SimpleGraph V) (f : Fin 5 → V) : Finset V :=
  (patternVertexSet f)ᶜ.filter (fun y => GemRightIndices (patternNeighborIndices G f y))

theorem gem_double_outer_partition {f : Fin 5 → V}
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn : 9 ≤ Fintype.card V) (hf : PatternEmbedding G patternGem f) :
    doubleOuterVertices G f = gemLeftVertices G f ∪ gemRightVertices G f := by
  ext y
  simp only [doubleOuterVertices, gemLeftVertices, gemRightVertices,
    Finset.mem_filter, Finset.mem_compl, Finset.mem_union]
  constructor
  · rintro ⟨hy, hcard⟩
    obtain ⟨w, hwS, hwy⟩ := exists_deletedVertex_away hn f {y} (by simp)
    have hfw : ∀ i, f i ≠ w := by
      intro i hi
      apply hwS
      rw [← hi]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hyw : y ≠ w := by
      intro hi
      apply hwy
      simp [← hi]
    have hyout : ∀ i, y ≠ f i := by
      intro i hi
      apply hy
      rw [hi]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit w
    obtain ⟨q, _, hq, hno⟩ := pattern_coloring_attachment_constraints
      hr hf patternGem_hamilton w c hfw y hyw hyout
    rcases gem_attachment_table q (patternNeighborIndices G f y) hq hcard hno with
      ⟨_, hl⟩ | ⟨_, hright⟩
    · exact Or.inl ⟨hy, hl⟩
    · exact Or.inr ⟨hy, hright⟩
  · rintro (⟨hy, hl⟩ | ⟨hy, hright⟩)
    · exact ⟨hy, gem_left_card_two _ hl⟩
    · exact ⟨hy, gem_right_card_two _ hright⟩

theorem gem_left_right_vertices_disjoint (f : Fin 5 → V) :
    Disjoint (gemLeftVertices G f) (gemRightVertices G f) := by
  apply Finset.disjoint_left.mpr
  intro y hleft hright
  exact gem_left_right_disjoint _ (Finset.mem_filter.mp hleft).2
    (Finset.mem_filter.mp hright).2

end TaskH.Five

#print axioms TaskH.Five.gem_left_right_disjoint
#print axioms TaskH.Five.gem_left_card_two
#print axioms TaskH.Five.gem_right_card_two
#print axioms TaskH.Five.star_double_neighbor_forced
#print axioms TaskH.Five.gem_left_neighbor_forced
#print axioms TaskH.Five.gem_right_neighbor_forced
#print axioms TaskH.Five.gem_double_outer_partition
#print axioms TaskH.Five.gem_left_right_vertices_disjoint
