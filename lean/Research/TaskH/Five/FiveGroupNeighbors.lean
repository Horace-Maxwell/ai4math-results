import Research.TaskH.Five.FivePatternExactness
import Research.TaskH.Five.FivePatternCrossPaths

/-! Neighbor-index classes supply actual cross paths, including the anchor. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

def StarIndices (A : Finset (Fin 5)) : Prop := A = {0, 1} ∨ A = {2, 3}

theorem patternNeighborIndices_eq_row {P : Finset (Sym2 (Fin 5))} {f : Fin 5 → V}
    (hf : PatternExactEmbedding G P f) (i : Fin 5) :
    patternNeighborIndices G f (f i) =
      (Finset.univ : Finset (Fin 5)).filter (fun j => s(i, j) ∈ P) := by
  ext j
  simp only [patternNeighborIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hf.2 i j, hf.1.2 i j⟩

theorem star_anchor_indices {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternStar f) :
    StarIndices (patternNeighborIndices G f (f 4)) := by
  rw [patternNeighborIndices_eq_row hf]
  unfold StarIndices
  decide +kernel

theorem gem_left_anchor_indices {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternGem f) :
    GemLeftIndices (patternNeighborIndices G f (f 0)) := by
  rw [patternNeighborIndices_eq_row hf]
  unfold GemLeftIndices
  decide +kernel

theorem gem_right_anchor_indices {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternGem f) :
    GemRightIndices (patternNeighborIndices G f (f 3)) := by
  rw [patternNeighborIndices_eq_row hf]
  unfold GemRightIndices
  decide +kernel

variable [Fintype V]

theorem star_double_neighbor_indices {f : Fin 5 → V}
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hf : PatternEmbedding G patternStar f)
    (y : V) (hy : y ∉ patternVertexSet f)
    (hcard : (patternNeighborIndices G f y).card = 2) :
    StarIndices (patternNeighborIndices G f y) := by
  obtain ⟨w, hwS, hwy⟩ := exists_deletedVertex_away hn9 f {y} (by simp)
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
  obtain ⟨q, _, hqA, hno⟩ := pattern_coloring_attachment_constraints
    hr hf patternStar_hamilton w c hfw y hyw hyout
  exact (star_attachment_table q (patternNeighborIndices G f y) hqA hcard hno).2

theorem star_attached_cross_paths {f : Fin 5 → V}
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hf : PatternExactEmbedding G patternStar f) :
    ∀ x ∈ attachedGroup f 4 (doubleOuterVertices G f),
      ∀ y ∈ attachedGroup f 4 (doubleOuterVertices G f), x ≠ y →
      ∃ i j : Fin 5, G.Adj x (f i) ∧ G.Adj (f i) (f j) ∧ G.Adj (f j) y := by
  apply attachedGroup_cross_paths hf.1 4 (doubleOuterVertices G f) StarIndices
    (fun I J hI hJ => star_pairs_cross I J hI hJ) (star_anchor_indices hf)
  intro y hy
  have hh := Finset.mem_filter.mp hy
  exact star_double_neighbor_indices hcrit hr hn9 hf.1 y
    (Finset.mem_compl.mp hh.1) hh.2

theorem gem_left_attached_cross_paths {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternGem f) :
    ∀ x ∈ attachedGroup f 0 (gemLeftVertices G f),
      ∀ y ∈ attachedGroup f 0 (gemLeftVertices G f), x ≠ y →
      ∃ i j : Fin 5, G.Adj x (f i) ∧ G.Adj (f i) (f j) ∧ G.Adj (f j) y := by
  apply attachedGroup_cross_paths hf.1 0 (gemLeftVertices G f) GemLeftIndices
    (fun I J hI hJ => gem_left_pairs_cross I J hI hJ) (gem_left_anchor_indices hf)
  intro y hy
  exact (Finset.mem_filter.mp hy).2

theorem gem_right_attached_cross_paths {f : Fin 5 → V}
    (hf : PatternExactEmbedding G patternGem f) :
    ∀ x ∈ attachedGroup f 3 (gemRightVertices G f),
      ∀ y ∈ attachedGroup f 3 (gemRightVertices G f), x ≠ y →
      ∃ i j : Fin 5, G.Adj x (f i) ∧ G.Adj (f i) (f j) ∧ G.Adj (f j) y := by
  apply attachedGroup_cross_paths hf.1 3 (gemRightVertices G f) GemRightIndices
    (fun I J hI hJ => gem_right_pairs_cross I J hI hJ) (gem_right_anchor_indices hf)
  intro y hy
  exact (Finset.mem_filter.mp hy).2

end TaskH.Five

#print axioms TaskH.Five.patternNeighborIndices_eq_row
#print axioms TaskH.Five.star_anchor_indices
#print axioms TaskH.Five.gem_left_anchor_indices
#print axioms TaskH.Five.gem_right_anchor_indices
#print axioms TaskH.Five.star_double_neighbor_indices
#print axioms TaskH.Five.star_attached_cross_paths
#print axioms TaskH.Five.gem_left_attached_cross_paths
#print axioms TaskH.Five.gem_right_attached_cross_paths
