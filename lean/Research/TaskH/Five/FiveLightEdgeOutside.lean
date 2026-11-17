import Research.TaskH.Five.FiveLightEdgeDecagon
import Research.TaskH.Five.FivePatternTransport

/-! Actual outside witnesses on five cycle edges yield a genuine ten-cycle. -/

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem light_neighbor_indices_card_le_two [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 5 G) (hr : RainbowFiveCycles G)
    (hn : 7 ≤ Fintype.card V) {f : Fin 5 → V} (hf : IsPentagon G f)
    (x : V) (hxout : ∀ j, x ≠ f j) :
    (patternNeighborIndices G f x).card ≤ 2 := by
  classical
  have hb := rainbow_pentagon_neighbors_card_le_two hcrit hr hn f hf x hxout
  have he : (G.neighborFinset x).filter
      (fun z => CycleContains (pentagonEdges f) z) =
        (patternNeighborIndices G f x).image f := by
    ext z
    simp only [patternNeighborIndices, Finset.mem_filter, G.mem_neighborFinset,
      cycleContains_pentagonEdges_iff, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hxz, j, rfl⟩
      exact ⟨j, hxz, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, j, rfl⟩
  rw [he, Finset.card_image_of_injective _ hf.1] at hb
  exact hb

theorem light_outside_witnesses_injective
    (f x : Fin 5 → V)
    (hbound : ∀ y : V, (∀ j, y ≠ f j) →
      (patternNeighborIndices G f y).card ≤ 2)
    (hxout : ∀ i j : Fin 5, x i ≠ f j)
    (hl : ∀ i : Fin 5, G.Adj (f i) (x i))
    (hr : ∀ i : Fin 5, G.Adj (f (i + 1)) (x i)) :
    Function.Injective x := by
  classical
  intro i j he
  have hb := hbound (x i) (hxout i)
  have hi : i ∈ patternNeighborIndices G f (x i) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hl i).symm⟩
  have his : i + 1 ∈ patternNeighborIndices G f (x i) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hr i).symm⟩
  have hj : j ∈ patternNeighborIndices G f (x i) := by
    rw [he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hl j).symm⟩
  have hjs : j + 1 ∈ patternNeighborIndices G f (x i) := by
    rw [he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hr j).symm⟩
  exact light_two_neighbors_determine_edge (patternNeighborIndices G f (x i))
    i j hb hi his hj hjs

/-- A true five-cycle has an edge whose every common neighbor is on the
cycle. Both the outside-two-neighbor bound and the forbidden ten-cycle are
proved from their actual graph hypotheses. -/
theorem pentagon_exists_edge_without_outside_common
    [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hn : 7 ≤ Fintype.card V)
    (f : Fin 5 → V) (hf : IsPentagon G f) :
    ∃ i : Fin 5, ∀ x : V, G.Adj (f i) x → G.Adj (f (i + 1)) x →
      ∃ j : Fin 5, f j = x := by
  classical
  by_contra hnone
  have hex : ∀ i : Fin 5, ∃ x : V,
      (∀ j : Fin 5, x ≠ f j) ∧ G.Adj (f i) x ∧ G.Adj (f (i + 1)) x := by
    intro i
    by_contra hbad
    apply hnone
    refine ⟨i, ?_⟩
    intro x hix hisx
    by_contra hout
    apply hbad
    refine ⟨x, ?_, hix, hisx⟩
    intro j he
    exact hout ⟨j, he.symm⟩
  choose x hxout hl hr' using hex
  have hbound : ∀ y : V, (∀ j, y ≠ f j) →
      (patternNeighborIndices G f y).card ≤ 2 := by
    intro y hy
    exact light_neighbor_indices_card_le_two hcrit hr hn hf y hy
  have hxin : Function.Injective x :=
    light_outside_witnesses_injective f x hbound hxout hl hr'
  exact shortFive_forbids_interleaved_neighbors hs f x hf.1 hxin hxout hl
    (fun i => (hr' i).symm)

end TaskH.Five

#print axioms TaskH.Five.light_neighbor_indices_card_le_two
#print axioms TaskH.Five.light_outside_witnesses_injective
#print axioms TaskH.Five.pentagon_exists_edge_without_outside_common
