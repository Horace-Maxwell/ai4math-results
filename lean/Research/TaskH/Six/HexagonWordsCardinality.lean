import Research.TaskH.Six.HexagonWords

/-!
Exact twelve-to-one counting for actual ordered hexagons. The image consists
only of true six-cycle edge sets, and is only a subset of all mod-six cycles
unless a separate ShortSixCycles proof has been supplied.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

open scoped Classical in
theorem hexagonWords_fiber_eq_orbit (f : Fin 6 → V) (hf : IsHexagon G f) :
    (hexagonWords G).filter (fun g => hexagonEdges g = hexagonEdges f) =
      Finset.univ.image (fun o : Bool × Fin 6 => f ∘ hexagonOrientedIndex o.1 o.2) := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨hword, he⟩ := Finset.mem_filter.mp hg
    obtain ⟨o, ho⟩ := hexagon_same_edges_reindex f g hf
      ((mem_hexagonWords_iff g).mp hword) he
    exact Finset.mem_image.mpr ⟨o, Finset.mem_univ _, ho.symm⟩
  · intro hg
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_filter.mpr ⟨(mem_hexagonWords_iff _).mpr (isHexagon_reindex f hf o),
      hexagonEdges_reindex f o⟩

open scoped Classical in
theorem hexagonWords_fiber_card (s : Finset (Sym2 V)) (hs : s ∈ actualSixEdgeSets G) :
    ((hexagonWords G).filter (fun f => hexagonEdges f = s)).card = 12 := by
  classical
  obtain ⟨f, hf, rfl⟩ := (mem_actualSixEdgeSets_iff s).mp hs
  rw [hexagonWords_fiber_eq_orbit f hf,
    Finset.card_image_of_injective _ (hexagon_reindex_parameters_injective f hf.1),
    Finset.card_univ]
  norm_num

theorem hexagonWords_card_eq_twelve_mul_actualSixEdgeSets_card :
    (hexagonWords G).card = 12 * (actualSixEdgeSets G).card := by
  classical
  calc
    (hexagonWords G).card = ∑ s ∈ actualSixEdgeSets G,
        ((hexagonWords G).filter (fun f => hexagonEdges f = s)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro f hf
      exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    _ = ∑ _s ∈ actualSixEdgeSets G, 12 :=
      Finset.sum_congr rfl (fun s hs => hexagonWords_fiber_card s hs)
    _ = 12 * (actualSixEdgeSets G).card := by simp [Nat.mul_comm]

theorem actualSixEdgeSets_subset_modCycleEdgeSets :
    (actualSixEdgeSets G : Set (Finset (Sym2 V))) ⊆ ModCycleEdgeSets 6 G := by
  classical
  intro s hs
  obtain ⟨f, hf, rfl⟩ := (mem_actualSixEdgeSets_iff s).mp hs
  exact hexagonEdges_mem_modCycleEdgeSets f hf

theorem actualSixEdgeSets_card_le_modCycleCount :
    (actualSixEdgeSets G).card ≤ modCycleCount 6 G := by
  classical
  have hh := Set.ncard_le_ncard (actualSixEdgeSets_subset_modCycleEdgeSets (G := G))
    (Basics.modCycleEdgeSets_finite 6 G)
  simpa only [Set.ncard_coe_finset, modCycleCount] using hh

theorem hexagonWords_card_le_twelve_mul_modCycleCount :
    (hexagonWords G).card ≤ 12 * modCycleCount 6 G := by
  rw [hexagonWords_card_eq_twelve_mul_actualSixEdgeSets_card]
  exact Nat.mul_le_mul_left 12 (actualSixEdgeSets_card_le_modCycleCount (G := G))

theorem actualSixEdgeSets_eq_modCycleEdgeSets_of_short (hs : ShortSixCycles G) :
    (actualSixEdgeSets G : Set (Finset (Sym2 V))) = ModCycleEdgeSets 6 G := by
  classical
  apply Set.Subset.antisymm actualSixEdgeSets_subset_modCycleEdgeSets
  intro s hmem
  obtain ⟨v, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  obtain ⟨f, hf, hfe⟩ := exists_hexagon_of_cycle_length_six hp (hs p hp hk)
  exact (mem_actualSixEdgeSets_iff s).mpr ⟨f, hf, hfe.trans he⟩

theorem actualSixEdgeSets_card_eq_modCycleCount_of_short (hs : ShortSixCycles G) :
    (actualSixEdgeSets G).card = modCycleCount 6 G := by
  classical
  rw [modCycleCount, ← actualSixEdgeSets_eq_modCycleEdgeSets_of_short hs,
    Set.ncard_coe_finset]

theorem hexagonWords_card_eq_twelve_mul_modCycleCount_of_short (hs : ShortSixCycles G) :
    (hexagonWords G).card = 12 * modCycleCount 6 G := by
  rw [hexagonWords_card_eq_twelve_mul_actualSixEdgeSets_card,
    actualSixEdgeSets_card_eq_modCycleCount_of_short hs]

end TaskH.Six

#print axioms TaskH.Six.hexagonWords_fiber_eq_orbit
#print axioms TaskH.Six.hexagonWords_fiber_card
#print axioms TaskH.Six.hexagonWords_card_eq_twelve_mul_actualSixEdgeSets_card
#print axioms TaskH.Six.actualSixEdgeSets_subset_modCycleEdgeSets
#print axioms TaskH.Six.actualSixEdgeSets_card_le_modCycleCount
#print axioms TaskH.Six.hexagonWords_card_le_twelve_mul_modCycleCount
#print axioms TaskH.Six.actualSixEdgeSets_eq_modCycleEdgeSets_of_short
#print axioms TaskH.Six.actualSixEdgeSets_card_eq_modCycleCount_of_short
#print axioms TaskH.Six.hexagonWords_card_eq_twelve_mul_modCycleCount_of_short
