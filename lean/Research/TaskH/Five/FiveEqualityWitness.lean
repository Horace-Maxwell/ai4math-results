import Research.TaskH.Five.FiveIncidence

/-! Extract an actual pentagon from the original nonzero cycle-edge-set count. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge

theorem equality_exists_pentagon {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hs : ShortFiveCycles G) (hc : modCycleCount 5 G = 72) :
    ∃ f : Fin 5 → V, IsPentagon G f := by
  classical
  have hn : 0 < (cycleFinset G).card := by rw [cycleFinset_card, hc]; omega
  obtain ⟨s, hmem⟩ := Finset.card_pos.mp hn
  obtain ⟨_v, p, hp, _he, hdiv⟩ :=
    Basics.mem_modCycleEdgeSets_iff.mp ((mem_cycleFinset s).mp hmem)
  exact ⟨cycleFiveVertices p, cycleFiveVertices_isPentagon hp (hs p hp hdiv)⟩

end TaskH.Five

#print axioms TaskH.Five.equality_exists_pentagon
