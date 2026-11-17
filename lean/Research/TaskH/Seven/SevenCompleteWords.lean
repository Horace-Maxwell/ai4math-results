import Research.TaskH.CycleFourWitness
import Research.TaskH.Seven.SevenHeptagonWordsCardinality

/-!
The complete eight-vertex graph has 40320 ordered injective seven-vertex
words, counted symbolically by the embedding-cardinality theorem. Its actual
unoriented seven-cycle edge sets are obtained by the proved fourteen-word fibers.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

theorem length_seven_of_mod_seven_of_card_le_thirteen [Fintype V] {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) (hk : 7 ∣ p.length)
    (hn : Fintype.card V ≤ 13) : p.length = 7 := by
  have hl := TaskH.FourCount.cycle_length_le_card hp
  have hp3 := hp.three_le_length
  obtain ⟨t, ht⟩ := hk
  omega

theorem shortSevenCycles_of_card_le_thirteen [Fintype V]
    (hn : Fintype.card V ≤ 13) : ShortSevenCycles G := by
  intro v p hp hk
  exact length_seven_of_mod_seven_of_card_le_thirteen hp hk hn

noncomputable def completeEightHeptagonWords : Finset (Fin 7 → Fin 8) := by
  classical
  exact Finset.univ.image (fun e : Fin 7 ↪ Fin 8 => (e : Fin 7 → Fin 8))

theorem heptagonWords_completeEight :
    heptagonWords (⊤ : SimpleGraph (Fin 8)) = completeEightHeptagonWords := by
  classical
  ext f
  constructor
  · intro hf
    have hi := ((mem_heptagonWords_iff f).mp hf).1
    exact Finset.mem_image.mpr ⟨⟨f, hi⟩, Finset.mem_univ _, rfl⟩
  · intro hf
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hf
    apply (mem_heptagonWords_iff _).mpr
    refine ⟨e.injective, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals exact e.injective.ne (by decide)

theorem completeEightHeptagonWords_card : completeEightHeptagonWords.card = 40320 := by
  classical
  have hinj : Function.Injective (fun e : Fin 7 ↪ Fin 8 => (e : Fin 7 → Fin 8)) := by
    intro e f he
    exact DFunLike.coe_injective he
  rw [completeEightHeptagonWords, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_embedding_eq]
  norm_num [Nat.descFactorial]

theorem completeEight_modCycleCount : modCycleCount 7 (⊤ : SimpleGraph (Fin 8)) = 2880 := by
  have hs : ShortSevenCycles (⊤ : SimpleGraph (Fin 8)) :=
    shortSevenCycles_of_card_le_thirteen (by decide)
  have hh := heptagonWords_card_eq_fourteen_mul_modCycleCount_of_short hs
  rw [heptagonWords_completeEight, completeEightHeptagonWords_card] at hh
  omega

end TaskH.Seven

#print axioms TaskH.Seven.length_seven_of_mod_seven_of_card_le_thirteen
#print axioms TaskH.Seven.shortSevenCycles_of_card_le_thirteen
#print axioms TaskH.Seven.completeEightHeptagonWords
#print axioms TaskH.Seven.heptagonWords_completeEight
#print axioms TaskH.Seven.completeEightHeptagonWords_card
#print axioms TaskH.Seven.completeEight_modCycleCount
