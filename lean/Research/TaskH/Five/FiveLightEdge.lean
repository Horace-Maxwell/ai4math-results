import Research.TaskH.Five.FiveLightEdgeTransport

/-! Every actual five-cycle has a light edge under the established graph
conclusions. The gem-free hypothesis is supplied by the separate forbidden
pattern theorem, rather than built into the original equality contract. -/

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} {G : SimpleGraph V}

def IsLightPentagonEdge (G : SimpleGraph V) (f : Fin 5 → V) (i : Fin 5) : Prop :=
  (∀ w : V, G.Adj (f i) w → G.Adj (f (i + 1)) w →
    ∃ j : Fin 5, f j = w) ∧
  (G.commonNeighbors (f i) (f (i + 1))).ncard ≤ 1

theorem pentagon_succ_adj {f : Fin 5 → V} (hf : IsPentagon G f) (i : Fin 5) :
    G.Adj (f i) (f (i + 1)) := by
  fin_cases i
  · exact hf.2.1
  · exact hf.2.2.1
  · exact hf.2.2.2.1
  · exact hf.2.2.2.2.1
  · exact hf.2.2.2.2.2

theorem pentagon_has_light_edge [Fintype V] [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 5 G) (hs : ShortFiveCycles G)
    (hr : RainbowFiveCycles G) (hn : 7 ≤ Fintype.card V)
    (hgem : ∀ r : Fin 5 → V, ¬ PatternEmbedding G patternGem r)
    (f : Fin 5 → V) (hf : IsPentagon G f) :
    ∃ i : Fin 5, G.Adj (f i) (f (i + 1)) ∧ IsLightPentagonEdge G f i := by
  classical
  let A := lightActualChords G f
  by_cases hsmall : A.card ≤ 1
  · obtain ⟨i, hout⟩ :=
      pentagon_exists_edge_without_outside_common hcrit hs hr hn f hf
    have hi : (lightIndexCommon (lightIndexEdges A) i (i + 1)).card ≤ 1 :=
      light_one_chord_common_le_one A hsmall i
    exact ⟨i, pentagon_succ_adj hf i, hout,
      light_common_card_bound hf i (i + 1) hout hi⟩
  · have hlarge : 2 ≤ A.card := by omega
    rcases light_many_chords_hook_or_gem A hlarge with hhook | hhasgem
    · obtain ⟨i, hi, hhook⟩ := hhook
      have hout : ∀ w : V, G.Adj (f i) w → G.Adj (f (i + 1)) w →
          ∃ j : Fin 5, f j = w := by
        intro w hu hv
        rcases hhook with hhook | hhook
        · exact light_hook_forbids_outside_common hf hgem i (i + 1) hhook w hu hv
        · exact light_hook_forbids_outside_common hf hgem (i + 1) i hhook w hv hu
      exact ⟨i, pentagon_succ_adj hf i, hout,
        light_common_card_bound hf i (i + 1) hout hi⟩
    · obtain ⟨g, hg⟩ := hhasgem
      exact (hgem (f ∘ g) (light_index_gem_embedding hf g hg)).elim

end TaskH.Five

#print axioms TaskH.Five.IsLightPentagonEdge
#print axioms TaskH.Five.pentagon_succ_adj
#print axioms TaskH.Five.pentagon_has_light_edge
