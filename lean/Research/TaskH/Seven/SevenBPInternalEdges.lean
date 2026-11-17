import Research.TaskH.Seven.SevenBPActualChordCount

/-! True unoriented internal edges split into the sixteen cycle edges and
all actual chords. This is the counting interface for the separate lower bound. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
variable {V : Type u} {G : SimpleGraph V}

noncomputable def cycleSixteenEdges (u : Fin 16 → V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.image (fun i : Fin 16 => s(u i, u (i + 1)))

noncomputable def actualInternalEdges (G : SimpleGraph V) (u : Fin 16 → V) : Finset (Sym2 V) := by
  classical
  exact ((Finset.univ : Finset (Fin 16 × Fin 16)).filter
    (fun p => G.Adj (u p.1) (u p.2))).image (fun p => s(u p.1, u p.2))

theorem cycleSixteenEdges_card (u : Fin 16 → V) (hu : Function.Injective u) :
    (cycleSixteenEdges u).card = 16 := by
  classical
  have hi : Function.Injective (fun i : Fin 16 => s(u i, u (i + 1))) := by
    intro i j he
    have ht : ∀ i j : Fin 16, s(i, i + 1) = s(j, j + 1) → i = j := by decide +kernel
    apply ht i j
    apply Sym2.map.injective hu
    simpa using he
  simpa only [cycleSixteenEdges, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_image_of_injective (Finset.univ : Finset (Fin 16)) hi)

theorem cycleSixteenEdges_disjoint_actualChordEdges (u : Fin 16 → V)
    (hu : Function.Injective u) : Disjoint (cycleSixteenEdges u) (actualChordEdges G u) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e he hc
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
  obtain ⟨j, k, _ha, hn, hp, hjk⟩ := (mem_actualChordEdges_iff u e).mp hc
  have hpair : s(i, i + 1) = s(j, k) := by
    apply Sym2.map.injective hu
    simpa using hi.trans hjk.symm
  have hindices : (i = j ∧ i + 1 = k) ∨ (i = k ∧ i + 1 = j) := by
    simpa only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] using hpair
  rcases hindices with ⟨hij, hk⟩ | ⟨hik, hj⟩
  · apply hn
    simpa only [← hij] using hk.symm
  · apply hp
    simpa only [← hik] using hj.symm

open scoped Classical in
theorem actualInternalEdges_eq_cycle_union_chord (u : Fin 16 → V)
    (hu : IsCycleSixteen G u) :
    actualInternalEdges G u = cycleSixteenEdges u ∪ actualChordEdges G u := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨⟨i, j⟩, hp, rfl⟩ := Finset.mem_image.mp he
    have ha := (Finset.mem_filter.mp hp).2
    by_cases hn : j = i + 1
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [hn]⟩
    · by_cases hp : i = j + 1
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [hp]; exact Sym2.eq_swap⟩
      · exact Finset.mem_union_right _ (actualChordEdges_mem_of_nonconsecutive_adj u i j ha hn hp)
  · intro he
    rcases Finset.mem_union.mp he with he | hc
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨(i, i + 1),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu.2 i⟩, rfl⟩
    · obtain ⟨i, j, ha, _hn, _hp, heq⟩ := (mem_actualChordEdges_iff u e).mp hc
      exact Finset.mem_image.mpr ⟨(i, j),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, heq⟩

theorem actualInternalEdges_card (u : Fin 16 → V) (hu : IsCycleSixteen G u) :
    (actualInternalEdges G u).card = 16 + (actualChordEdges G u).card := by
  classical
  rw [actualInternalEdges_eq_cycle_union_chord u hu,
    Finset.card_union_of_disjoint (cycleSixteenEdges_disjoint_actualChordEdges u hu.1),
    cycleSixteenEdges_card u hu.1]

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.cycleSixteenEdges
#print axioms TaskH.Seven.BP.actualInternalEdges
#print axioms TaskH.Seven.BP.cycleSixteenEdges_card
#print axioms TaskH.Seven.BP.cycleSixteenEdges_disjoint_actualChordEdges
#print axioms TaskH.Seven.BP.actualInternalEdges_eq_cycle_union_chord
#print axioms TaskH.Seven.BP.actualInternalEdges_card
