import Research.TaskH.Five.FiveGroupNeighbors

/-! Each actual forced-color attachment class has at most two exterior vertices. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem star_doubleOuter_card_le_two
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hn22 : Fintype.card V ≤ 22)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    {f : Fin 5 → V} (hf : PatternExactEmbedding G patternStar f) :
    (doubleOuterVertices G f).card ≤ 2 := by
  apply attachedGroup_card_le_two hcrit hr hn9 hn22 f 4 (doubleOuterVertices G f)
    (patternVertexSet_card hf.1)
  · intro y hy
    exact (Finset.mem_filter.mp hy).1
  · intro y hy
    have hh := Finset.mem_filter.mp hy
    exact star_double_neighbor_forced hr hf.1 y (Finset.mem_compl.mp hh.1) hh.2
  · exact hdeg
  · rw [star_anchor_internal_degree hf]
  · intro y hy
    rw [patternNeighborIndices_card hf.1]
    exact le_of_eq (Finset.mem_filter.mp hy).2
  · exact star_attached_cross_paths hcrit hr hn9 hf

theorem gem_left_card_le_two
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hn22 : Fintype.card V ≤ 22)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    {f : Fin 5 → V} (hf : PatternExactEmbedding G patternGem f) :
    (gemLeftVertices G f).card ≤ 2 := by
  apply attachedGroup_card_le_two hcrit hr hn9 hn22 f 0 (gemLeftVertices G f)
    (patternVertexSet_card hf.1)
  · intro y hy
    exact (Finset.mem_filter.mp hy).1
  · intro y hy
    have hh := Finset.mem_filter.mp hy
    exact gem_left_neighbor_forced hr hf.1 y (Finset.mem_compl.mp hh.1) hh.2
  · exact hdeg
  · rw [gem_left_anchor_internal_degree hf]
  · intro y hy
    rw [patternNeighborIndices_card hf.1]
    exact le_of_eq (gem_left_card_two _ (Finset.mem_filter.mp hy).2)
  · exact gem_left_attached_cross_paths hf

theorem gem_right_card_le_two
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hn22 : Fintype.card V ≤ 22)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    {f : Fin 5 → V} (hf : PatternExactEmbedding G patternGem f) :
    (gemRightVertices G f).card ≤ 2 := by
  apply attachedGroup_card_le_two hcrit hr hn9 hn22 f 3 (gemRightVertices G f)
    (patternVertexSet_card hf.1)
  · intro y hy
    exact (Finset.mem_filter.mp hy).1
  · intro y hy
    have hh := Finset.mem_filter.mp hy
    exact gem_right_neighbor_forced hr hf.1 y (Finset.mem_compl.mp hh.1) hh.2
  · exact hdeg
  · rw [gem_right_anchor_internal_degree hf]
  · intro y hy
    rw [patternNeighborIndices_card hf.1]
    exact le_of_eq (gem_right_card_two _ (Finset.mem_filter.mp hy).2)
  · exact gem_right_attached_cross_paths hf

theorem gem_doubleOuter_card_le_four
    (hcrit : Challenge.IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn9 : 9 ≤ Fintype.card V) (hn22 : Fintype.card V ≤ 22)
    (hdeg : ∀ v : V, 6 ≤ G.degree v)
    {f : Fin 5 → V} (hf : PatternExactEmbedding G patternGem f) :
    (doubleOuterVertices G f).card ≤ 4 := by
  have hleft := gem_left_card_le_two hcrit hr hn9 hn22 hdeg hf
  have hright := gem_right_card_le_two hcrit hr hn9 hn22 hdeg hf
  rw [gem_double_outer_partition hcrit hr hn9 hf.1]
  have hb := Finset.card_union_le (gemLeftVertices G f) (gemRightVertices G f)
  omega

end TaskH.Five

#print axioms TaskH.Five.star_doubleOuter_card_le_two
#print axioms TaskH.Five.gem_left_card_le_two
#print axioms TaskH.Five.gem_right_card_le_two
#print axioms TaskH.Five.gem_doubleOuter_card_le_four
