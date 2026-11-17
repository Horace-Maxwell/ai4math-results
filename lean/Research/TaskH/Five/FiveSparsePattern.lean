import Research.TaskH.Five.FivePatternTransport

/-! Actual graph exclusion of the two sparse-attachment five-point patterns. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_deletedVertex_away (hn : 9 ≤ Fintype.card V)
    (f : Fin 5 → V) (T : Finset V) (hT : T.card ≤ 3) :
    ∃ w : V, w ∉ patternVertexSet f ∧ w ∉ T := by
  have hS : (patternVertexSet f).card ≤ 5 := by
    simpa only [patternVertexSet, Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin 5))) (f := f))
  have hh := Finset.card_union_le (patternVertexSet f) T
  have hlt : (patternVertexSet f ∪ T).card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    omega
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨w, fun h => hw (Finset.mem_union_left _ h),
    fun h => hw (Finset.mem_union_right _ h)⟩

theorem patternVertexSet_hamilton {P : Finset (Sym2 (Fin 5))}
    {f : Fin 5 → V} {h : Fin 5 → Fin 5} (hh : PatternHamilton P h) :
    patternVertexSet f = TaskH.cycleVertices (pentagonEdges (f ∘ h)) := by
  rw [cycleVertices_pentagonEdges]
  ext x
  simp only [patternVertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := Finite.surjective_of_injective hh.1 i
    exact ⟨j, congrArg f hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨h j, hj⟩

theorem pattern_outer_neighbors_le_two {P : Finset (Sym2 (Fin 5))}
    {f : Fin 5 → V} {h : Fin 5 → Fin 5}
    (hcrit : IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn : 7 ≤ Fintype.card V) (hf : PatternEmbedding G P f)
    (hh : PatternHamilton P h) (y : V) (hy : y ∉ patternVertexSet f) :
    (patternNeighborIndices G f y).card ≤ 2 := by
  have hyout : ∀ i, y ≠ f i := by
    intro i hiy
    apply hy
    rw [hiy]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hp := patternHamilton_isPentagon hf hh
  have hb := rainbow_pentagon_neighbors_card_le_two hcrit hr hn (f ∘ h) hp y
    (fun i => hyout (h i))
  have he : neighborsIn G (patternVertexSet f) y =
      (G.neighborFinset y).filter (fun x => CycleContains (pentagonEdges (f ∘ h)) x) := by
    ext x
    simp only [neighborsIn, Finset.mem_filter, G.mem_neighborFinset,
      patternVertexSet_hamilton hh, TaskH.mem_cycleVertices]
    exact and_comm
  rw [← patternNeighborIndices_card hf, he]
  exact hb

theorem no_pattern_of_no_two_attachment {P : Finset (Sym2 (Fin 5))}
    {h : Fin 5 → Fin 5}
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hn : 9 ≤ Fintype.card V)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard)
    (hh : PatternHamilton P h)
    (htable : ∀ (q : Fin 5) (A : Finset (Fin 5)), q ∉ A → A.card = 2 →
      PatternNoThreePath P q A → False) :
    ∀ f : Fin 5 → V, ¬ PatternEmbedding G P f := by
  intro f hf
  apply no_sparse_five_vertex_set hs hc (by omega) h13 hsingle
    (patternVertexSet f) (patternVertexSet_card hf)
  intro y hy
  have hyS : y ∉ patternVertexSet f := Finset.mem_compl.mp hy
  rw [patternNeighborIndices_card hf]
  have htwo := pattern_outer_neighbors_le_two hcrit hr (by omega) hf hh y hyS
  by_contra hnot
  have hcard : (patternNeighborIndices G f y).card = 2 := by omega
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
    apply hyS
    rw [hi]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨c⟩ := TaskH.critical_colorable_deletedVertex hcrit w
  obtain ⟨q, _, hq, hno⟩ :=
    pattern_coloring_attachment_constraints hr hf hh w c hfw y hyw hyout
  exact htable q (patternNeighborIndices G f y) hq hcard hno

theorem no_nearComplete_pattern
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hn : 9 ≤ Fintype.card V)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard) :
    ∀ f : Fin 5 → V, ¬ PatternEmbedding G patternNearComplete f :=
  no_pattern_of_no_two_attachment hcrit hs hr hc hn h13 hsingle
    patternNearComplete_hamilton nearComplete_no_attachment

theorem no_missingMatching_pattern
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hc : modCycleCount 5 G = 72)
    (hn : 9 ≤ Fintype.card V)
    (h13 : ∀ v : V, 13 ≤ cycleDegree G v)
    (hsingle : ∀ v : V, 12 * (10 - G.degree v) ≤
      (TaskH.modCyclesThrough 5 G v).ncard) :
    ∀ f : Fin 5 → V, ¬ PatternEmbedding G patternMissingMatching f :=
  no_pattern_of_no_two_attachment hcrit hs hr hc hn h13 hsingle
    patternMissingMatching_hamilton missingMatching_no_attachment

end TaskH.Five

#print axioms TaskH.Five.exists_deletedVertex_away
#print axioms TaskH.Five.patternVertexSet_hamilton
#print axioms TaskH.Five.pattern_outer_neighbors_le_two
#print axioms TaskH.Five.no_pattern_of_no_two_attachment
#print axioms TaskH.Five.no_nearComplete_pattern
#print axioms TaskH.Five.no_missingMatching_pattern
