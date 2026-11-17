import Research.TaskH.Seven.SevenHeptagonWords

/-!
Exact fourteen-to-one counting for actual ordered heptagons. The image consists
only of true seven-cycle edge sets, and is only a subset of all mod-seven cycles
unless a separate ShortSevenCycles proof has been supplied.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

open scoped Classical in
theorem heptagonWords_fiber_eq_orbit (f : Fin 7 → V) (hf : IsHeptagon G f) :
    (heptagonWords G).filter (fun g => heptagonEdges g = heptagonEdges f) =
      Finset.univ.image (fun o : Bool × Fin 7 => f ∘ heptagonOrientedIndex o.1 o.2) := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨hword, he⟩ := Finset.mem_filter.mp hg
    obtain ⟨o, ho⟩ := heptagon_same_edges_reindex f g hf
      ((mem_heptagonWords_iff g).mp hword) he
    exact Finset.mem_image.mpr ⟨o, Finset.mem_univ _, ho.symm⟩
  · intro hg
    obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp hg
    exact Finset.mem_filter.mpr ⟨(mem_heptagonWords_iff _).mpr (isHeptagon_reindex f hf o),
      heptagonEdges_reindex f o⟩

open scoped Classical in
theorem heptagonWords_fiber_card (s : Finset (Sym2 V)) (hs : s ∈ actualSevenEdgeSets G) :
    ((heptagonWords G).filter (fun f => heptagonEdges f = s)).card = 14 := by
  classical
  obtain ⟨f, hf, rfl⟩ := (mem_actualSevenEdgeSets_iff s).mp hs
  rw [heptagonWords_fiber_eq_orbit f hf,
    Finset.card_image_of_injective _ (heptagon_reindex_parameters_injective f hf.1),
    Finset.card_univ]
  norm_num

theorem heptagonWords_card_eq_fourteen_mul_actualSevenEdgeSets_card :
    (heptagonWords G).card = 14 * (actualSevenEdgeSets G).card := by
  classical
  calc
    (heptagonWords G).card = ∑ s ∈ actualSevenEdgeSets G,
        ((heptagonWords G).filter (fun f => heptagonEdges f = s)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro f hf
      exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    _ = ∑ _s ∈ actualSevenEdgeSets G, 14 :=
      Finset.sum_congr rfl (fun s hs => heptagonWords_fiber_card s hs)
    _ = 14 * (actualSevenEdgeSets G).card := by simp [Nat.mul_comm]

theorem actualSevenEdgeSets_subset_modCycleEdgeSets :
    (actualSevenEdgeSets G : Set (Finset (Sym2 V))) ⊆ ModCycleEdgeSets 7 G := by
  classical
  intro s hs
  obtain ⟨f, hf, rfl⟩ := (mem_actualSevenEdgeSets_iff s).mp hs
  exact heptagonEdges_mem_modCycleEdgeSets f hf

theorem actualSevenEdgeSets_card_le_modCycleCount :
    (actualSevenEdgeSets G).card ≤ modCycleCount 7 G := by
  classical
  have hh := Set.ncard_le_ncard (actualSevenEdgeSets_subset_modCycleEdgeSets (G := G))
    (Basics.modCycleEdgeSets_finite 7 G)
  simpa only [Set.ncard_coe_finset, modCycleCount] using hh

theorem heptagonWords_card_le_fourteen_mul_modCycleCount :
    (heptagonWords G).card ≤ 14 * modCycleCount 7 G := by
  rw [heptagonWords_card_eq_fourteen_mul_actualSevenEdgeSets_card]
  exact Nat.mul_le_mul_left 14 (actualSevenEdgeSets_card_le_modCycleCount (G := G))

theorem actualSevenEdgeSets_eq_modCycleEdgeSets_of_short (hs : ShortSevenCycles G) :
    (actualSevenEdgeSets G : Set (Finset (Sym2 V))) = ModCycleEdgeSets 7 G := by
  classical
  apply Set.Subset.antisymm actualSevenEdgeSets_subset_modCycleEdgeSets
  intro s hmem
  obtain ⟨v, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  obtain ⟨f, hf, hfe⟩ := exists_heptagon_of_cycle_length_seven hp (hs p hp hk)
  exact (mem_actualSevenEdgeSets_iff s).mpr ⟨f, hf, hfe.trans he⟩

theorem actualSevenEdgeSets_card_eq_modCycleCount_of_short (hs : ShortSevenCycles G) :
    (actualSevenEdgeSets G).card = modCycleCount 7 G := by
  classical
  rw [modCycleCount, ← actualSevenEdgeSets_eq_modCycleEdgeSets_of_short hs,
    Set.ncard_coe_finset]

theorem heptagonWords_card_eq_fourteen_mul_modCycleCount_of_short (hs : ShortSevenCycles G) :
    (heptagonWords G).card = 14 * modCycleCount 7 G := by
  rw [heptagonWords_card_eq_fourteen_mul_actualSevenEdgeSets_card,
    actualSevenEdgeSets_card_eq_modCycleCount_of_short hs]

end TaskH.Seven

#print axioms TaskH.Seven.heptagonWords_fiber_eq_orbit
#print axioms TaskH.Seven.heptagonWords_fiber_card
#print axioms TaskH.Seven.heptagonWords_card_eq_fourteen_mul_actualSevenEdgeSets_card
#print axioms TaskH.Seven.actualSevenEdgeSets_subset_modCycleEdgeSets
#print axioms TaskH.Seven.actualSevenEdgeSets_card_le_modCycleCount
#print axioms TaskH.Seven.heptagonWords_card_le_fourteen_mul_modCycleCount
#print axioms TaskH.Seven.actualSevenEdgeSets_eq_modCycleEdgeSets_of_short
#print axioms TaskH.Seven.actualSevenEdgeSets_card_eq_modCycleCount_of_short
#print axioms TaskH.Seven.heptagonWords_card_eq_fourteen_mul_modCycleCount_of_short
