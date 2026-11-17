import Research.TaskH.Seven.SevenBPChordClassification

/-! The actual set of all unoriented, non-cycle edges inside the sixteen
specified cycle vertices. Every such edge is classified, and both chord images
are proved injective and disjoint before their cardinalities are added. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

noncomputable def actualChordEdges (G : SimpleGraph V) (u : Fin 16 → V) : Finset (Sym2 V) := by
  classical
  exact ((Finset.univ : Finset (Fin 16 × Fin 16)).filter
    (fun p => G.Adj (u p.1) (u p.2) ∧ p.2 ≠ p.1 + 1 ∧ p.1 ≠ p.2 + 1)).image
      (fun p => s(u p.1, u p.2))

noncomputable def actualFiveChordEdges (G : SimpleGraph V) (u : Fin 16 → V) : Finset (Sym2 V) := by
  classical
  exact (fiveChordIndices G u).image (fun i => s(u i, u (i + 5)))

noncomputable def actualSevenChordEdges (G : SimpleGraph V) (u : Fin 16 → V) : Finset (Sym2 V) := by
  classical
  exact (sevenChordIndices G u).image (fun i => s(u i, u (i + 7)))

theorem mem_actualChordEdges_iff (u : Fin 16 → V) (e : Sym2 V) :
    e ∈ actualChordEdges G u ↔ ∃ i j : Fin 16,
      G.Adj (u i) (u j) ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧ s(u i, u j) = e := by
  classical
  constructor
  · intro he
    obtain ⟨⟨i, j⟩, hp, heq⟩ := Finset.mem_image.mp he
    obtain ⟨ha, hn, hp⟩ := (Finset.mem_filter.mp hp).2
    exact ⟨i, j, ha, hn, hp, heq⟩
  · rintro ⟨i, j, ha, hn, hp, heq⟩
    exact Finset.mem_image.mpr ⟨(i, j),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hn, hp⟩, heq⟩

theorem actualChordEdges_mem_of_nonconsecutive_adj (u : Fin 16 → V) (i j : Fin 16)
    (ha : G.Adj (u i) (u j)) (hn : j ≠ i + 1) (hp : i ≠ j + 1) :
    s(u i, u j) ∈ actualChordEdges G u :=
  (mem_actualChordEdges_iff u _).mpr ⟨i, j, ha, hn, hp, rfl⟩

theorem five_chord_edge_injective (u : Fin 16 → V) (hu : Function.Injective u) :
    Function.Injective (fun i : Fin 16 => s(u i, u (i + 5))) := by
  intro i j he
  have ht : ∀ i j : Fin 16, s(i, i + 5) = s(j, j + 5) → i = j := by decide +kernel
  apply ht i j
  apply Sym2.map.injective hu
  simpa using he

theorem seven_chord_edge_injective (u : Fin 16 → V) (hu : Function.Injective u) :
    Function.Injective (fun i : Fin 16 => s(u i, u (i + 7))) := by
  intro i j he
  have ht : ∀ i j : Fin 16, s(i, i + 7) = s(j, j + 7) → i = j := by decide +kernel
  apply ht i j
  apply Sym2.map.injective hu
  simpa using he

theorem actualFiveChordEdges_card (u : Fin 16 → V) (hu : Function.Injective u) :
    (actualFiveChordEdges G u).card = (fiveChordIndices G u).card := by
  classical
  exact Finset.card_image_of_injective _ (five_chord_edge_injective u hu)

theorem actualSevenChordEdges_card (u : Fin 16 → V) (hu : Function.Injective u) :
    (actualSevenChordEdges G u).card = (sevenChordIndices G u).card := by
  classical
  exact Finset.card_image_of_injective _ (seven_chord_edge_injective u hu)

theorem actual_chord_families_disjoint (u : Fin 16 → V) (hu : Function.Injective u) :
    Disjoint (actualFiveChordEdges G u) (actualSevenChordEdges G u) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he5 he7
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he5
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp he7
  have heq : s(i, i + 5) = s(j, j + 7) := by
    apply Sym2.map.injective hu
    simpa using hi.trans hj.symm
  have ht : ∀ i j : Fin 16, s(i, i + 5) ≠ s(j, j + 7) := by decide +kernel
  exact ht i j heq

open scoped Classical in
theorem actualChordEdges_eq_five_union_seven (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G) :
    actualChordEdges G u = actualFiveChordEdges G u ∪ actualSevenChordEdges G u := by
  classical
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  ext e
  constructor
  · intro he
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ha, hn1, hp1⟩ := (Finset.mem_filter.mp hp).2
    rcases noncycle_adj_is_five_or_seven u hu hn c i j ha hn1 hp1 with h5 | h5 | h7 | h7
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨i, (mem_fiveChordIndices u i).mpr (by simpa only [FiveChord, h5] using ha),
        by rw [h5]⟩
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨j, (mem_fiveChordIndices u j).mpr (by simpa only [FiveChord, h5] using ha.symm),
        by rw [h5]; exact Sym2.eq_swap⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨i, (mem_sevenChordIndices u i).mpr (by simpa only [SevenChord, h7] using ha),
        by rw [h7]⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨j, (mem_sevenChordIndices u j).mpr (by simpa only [SevenChord, h7] using ha.symm),
        by rw [h7]; exact Sym2.eq_swap⟩
  · intro he
    rcases Finset.mem_union.mp he with he5 | he7
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he5
      apply Finset.mem_image.mpr
      refine ⟨(i, i + 5), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have ht : ∀ i : Fin 16, i + 5 ≠ i + 1 ∧ i ≠ (i + 5) + 1 := by decide +kernel
      exact ⟨(mem_fiveChordIndices u i).mp hi, (ht i).1, (ht i).2⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he7
      apply Finset.mem_image.mpr
      refine ⟨(i, i + 7), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have ht : ∀ i : Fin 16, i + 7 ≠ i + 1 ∧ i ≠ (i + 7) + 1 := by decide +kernel
      exact ⟨(mem_sevenChordIndices u i).mp hi, (ht i).1, (ht i).2⟩

theorem actualChordEdges_card_eq_five_add_seven (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G) :
    (actualChordEdges G u).card = (fiveChordIndices G u).card + (sevenChordIndices G u).card := by
  classical
  rw [actualChordEdges_eq_five_union_seven hb u hu hn,
    Finset.card_union_of_disjoint (actual_chord_families_disjoint u hu.1),
    actualFiveChordEdges_card u hu.1, actualSevenChordEdges_card u hu.1]

theorem actualChordEdges_card_le_eleven (hb : G.IsBipartite)
    (u : Fin 16 → V) (hu : IsCycleSixteen G u) (hn : NoFourteenCycle G) :
    (actualChordEdges G u).card ≤ 11 := by
  rw [actualChordEdges_card_eq_five_add_seven hb u hu hn]
  exact actual_five_seven_chord_card_le_eleven u hu hn

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.actualChordEdges
#print axioms TaskH.Seven.BP.actualFiveChordEdges
#print axioms TaskH.Seven.BP.actualSevenChordEdges
#print axioms TaskH.Seven.BP.mem_actualChordEdges_iff
#print axioms TaskH.Seven.BP.actualChordEdges_mem_of_nonconsecutive_adj
#print axioms TaskH.Seven.BP.five_chord_edge_injective
#print axioms TaskH.Seven.BP.seven_chord_edge_injective
#print axioms TaskH.Seven.BP.actualFiveChordEdges_card
#print axioms TaskH.Seven.BP.actualSevenChordEdges_card
#print axioms TaskH.Seven.BP.actual_chord_families_disjoint
#print axioms TaskH.Seven.BP.actualChordEdges_eq_five_union_seven
#print axioms TaskH.Seven.BP.actualChordEdges_card_eq_five_add_seven
#print axioms TaskH.Seven.BP.actualChordEdges_card_le_eleven
