import Research.TaskH.CaseSix
import Research.TaskH.CompleteCritical
import Research.TaskH.CycleFourWitness
import Research.TaskH.Six.HexagonWordsCardinality

/-!
The original K7 positive example. The 5040 ordered injective words are counted
symbolically by the fixed Mathlib embedding-cardinality theorem, then divided
by the proved twelve-word fibers. No family of arbitrary graphs is enumerated.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem length_six_of_mod_six_of_card_le_eleven [Fintype V] {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hk : 6 ∣ p.length)
    (hn : Fintype.card V ≤ 11) : p.length = 6 := by
  have hl := TaskH.FourCount.cycle_length_le_card hp
  have hp3 := hp.three_le_length
  obtain ⟨t, ht⟩ := hk
  omega

theorem shortSixCycles_of_card_le_eleven [Fintype V]
    (hn : Fintype.card V ≤ 11) : ShortSixCycles G := by
  intro v p hp hk
  exact length_six_of_mod_six_of_card_le_eleven hp hk hn

noncomputable def completeSevenHexagonWords : Finset (Fin 6 → Fin 7) := by
  classical
  exact Finset.univ.image (fun e : Fin 6 ↪ Fin 7 => (e : Fin 6 → Fin 7))

theorem hexagonWords_completeSeven :
    hexagonWords (⊤ : SimpleGraph (Fin 7)) = completeSevenHexagonWords := by
  classical
  ext f
  constructor
  · intro hf
    have hi := ((mem_hexagonWords_iff f).mp hf).1
    exact Finset.mem_image.mpr ⟨⟨f, hi⟩, Finset.mem_univ _, rfl⟩
  · intro hf
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hf
    apply (mem_hexagonWords_iff _).mpr
    refine ⟨e.injective, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals exact e.injective.ne (by decide)

theorem completeSevenHexagonWords_card : completeSevenHexagonWords.card = 5040 := by
  classical
  have hinj : Function.Injective (fun e : Fin 6 ↪ Fin 7 => (e : Fin 6 → Fin 7)) := by
    intro e f he
    exact DFunLike.coe_injective he
  rw [completeSevenHexagonWords, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_embedding_eq]
  norm_num [Nat.descFactorial]

theorem completeSeven_modCycleCount : modCycleCount 6 (⊤ : SimpleGraph (Fin 7)) = 420 := by
  have hs : ShortSixCycles (⊤ : SimpleGraph (Fin 7)) :=
    shortSixCycles_of_card_le_eleven (by decide)
  have hh := hexagonWords_card_eq_twelve_mul_modCycleCount_of_short hs
  rw [hexagonWords_completeSeven, completeSevenHexagonWords_card] at hh
  omega

theorem completeSeven_check : CompleteSevenCheck := by
  refine ⟨TaskH.complete_isCriticalPlus 6, completeSeven_modCycleCount, ?_⟩
  decide +kernel

end TaskH.Six

#print axioms TaskH.Six.length_six_of_mod_six_of_card_le_eleven
#print axioms TaskH.Six.shortSixCycles_of_card_le_eleven
#print axioms TaskH.Six.completeSevenHexagonWords
#print axioms TaskH.Six.hexagonWords_completeSeven
#print axioms TaskH.Six.completeSevenHexagonWords_card
#print axioms TaskH.Six.completeSeven_modCycleCount
#print axioms TaskH.Six.completeSeven_check
