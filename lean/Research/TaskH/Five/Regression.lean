import Research.TaskH.CaseFive
import Research.TaskH.CompleteCritical
import Research.TaskH.CycleFourWitness
import Research.TaskH.Five.CycleFive

/-! The independent original K6 positive example, with actual cycle edge sets. -/
set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

noncomputable def pentagonWords [Fintype V] (G : SimpleGraph V) :
    Finset (Fin 5 → V) := by
  classical
  exact Finset.univ.filter (IsPentagon G)

theorem length_five_of_mod_five_of_card_le_nine [Fintype V] {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hk : 5 ∣ p.length)
    (hn : Fintype.card V ≤ 9) : p.length = 5 := by
  have hl := TaskH.FourCount.cycle_length_le_card hp
  have hp3 := hp.three_le_length
  obtain ⟨t, ht⟩ := hk
  omega

theorem mem_modCycleEdgeSets_iff_mem_image_pentagonWords [Fintype V] [DecidableEq V]
    (hn : Fintype.card V ≤ 9) {s : Finset (Sym2 V)} :
    s ∈ ModCycleEdgeSets 5 G ↔ s ∈ (pentagonWords G).image pentagonEdges := by
  classical
  constructor
  · intro hs
    obtain ⟨v, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hs
    have hl := length_five_of_mod_five_of_card_le_nine hp hk hn
    obtain ⟨f, hf, hfe⟩ := exists_pentagon_of_cycle_length_five hp hl
    exact Finset.mem_image.mpr ⟨f,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, hfe.trans he⟩
  · intro hs
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp hs
    rw [← hfe]
    exact pentagonEdges_mem_modCycleEdgeSets f (Finset.mem_filter.mp hf).2

theorem modCycleCount_eq_image_pentagonWords_card [Fintype V] [DecidableEq V]
    (hn : Fintype.card V ≤ 9) :
    modCycleCount 5 G = ((pentagonWords G).image pentagonEdges).card := by
  classical
  have he : ModCycleEdgeSets 5 G =
      (((pentagonWords G).image pentagonEdges : Finset (Finset (Sym2 V))) :
        Set (Finset (Sym2 V))) := by
    ext s
    exact mem_modCycleEdgeSets_iff_mem_image_pentagonWords hn
  rw [modCycleCount, he, Set.ncard_coe_finset]

/-- A finite word family in one fixed complete graph; no graphs are enumerated. -/
def completeSixPentagonWords : Finset (Fin 5 → Fin 6) :=
  Finset.univ.filter Function.Injective

def completeSixCycleEdgeSets : Finset (Finset (Sym2 (Fin 6))) :=
  completeSixPentagonWords.image pentagonEdges

theorem completeSixCycleEdgeSets_card : completeSixCycleEdgeSets.card = 72 := by
  decide +kernel

theorem pentagonWords_completeSix : pentagonWords (⊤ : SimpleGraph (Fin 6)) =
    completeSixPentagonWords := by
  classical
  ext f
  simp only [pentagonWords, completeSixPentagonWords, Finset.mem_filter,
    Finset.mem_univ, true_and, IsPentagon, SimpleGraph.top_adj]
  constructor
  · exact And.left
  · intro hf
    exact ⟨hf, hf.ne (by decide), hf.ne (by decide), hf.ne (by decide),
      hf.ne (by decide), hf.ne (by decide)⟩

theorem completeSix_modCycleCount : modCycleCount 5 (⊤ : SimpleGraph (Fin 6)) = 72 := by
  rw [modCycleCount_eq_image_pentagonWords_card (by decide), pentagonWords_completeSix]
  exact completeSixCycleEdgeSets_card

theorem completeSix_check : CompleteSixCheck := by
  refine ⟨TaskH.complete_isCriticalPlus 5, completeSix_modCycleCount, ?_⟩
  decide +kernel

end TaskH.Five

#print axioms TaskH.Five.pentagonWords
#print axioms TaskH.Five.length_five_of_mod_five_of_card_le_nine
#print axioms TaskH.Five.mem_modCycleEdgeSets_iff_mem_image_pentagonWords
#print axioms TaskH.Five.modCycleCount_eq_image_pentagonWords_card
#print axioms TaskH.Five.completeSixPentagonWords
#print axioms TaskH.Five.completeSixCycleEdgeSets
#print axioms TaskH.Five.completeSixCycleEdgeSets_card
#print axioms TaskH.Five.pentagonWords_completeSix
#print axioms TaskH.Five.completeSix_modCycleCount
#print axioms TaskH.Five.completeSix_check
