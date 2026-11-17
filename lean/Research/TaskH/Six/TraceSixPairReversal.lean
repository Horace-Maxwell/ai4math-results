import Research.TaskH.Six.TraceSixPairIdentity

/-! Reversing both actual three-edge paths interchanges overlap classes 1/2 and 3/4. -/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

theorem traceThreePath_reverse (u v : V) (p : V × V)
    (hp : IsTraceThreePath G u v p) : IsTraceThreePath G v u (p.2, p.1) := by
  obtain ⟨hua, hub, huv, hab, hav, hbv⟩ :=
    (traceThreeWord_injective_iff u p.1 p.2 v).mp hp.1
  exact ⟨(traceThreeWord_injective_iff v p.2 p.1 u).mpr
    ⟨hbv.symm, hav.symm, huv.symm, hab.symm, hub.symm, hua.symm⟩,
    hp.2.2.2.symm, hp.2.2.1.symm, hp.2.1.symm⟩

def tracePairReverse (f : Fin 6 → V) : Fin 6 → V :=
  ![f 3, f 2, f 1, f 0, f 5, f 4]

theorem tracePairReverse_involutive (f : Fin 6 → V) :
    tracePairReverse (tracePairReverse f) = f := by
  funext i
  fin_cases i <;> rfl

theorem tracePairReverse_isPair (f : Fin 6 → V) (hf : IsTracePathPair G f) :
    IsTracePathPair G (tracePairReverse f) := by
  refine ⟨traceThreePath_reverse (f 0) (f 3) (f 1, f 2) hf.1,
    traceThreePath_reverse (f 0) (f 3) (f 5, f 4) hf.2.1, ?_⟩
  intro he
  exact hf.2.2 (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))

variable [Fintype V]

theorem tracePairReverse_mem_two_of_mem_one (f : Fin 6 → V)
    (hf : f ∈ traceOverlapWords G 1) : tracePairReverse f ∈ traceOverlapWords G 2 := by
  obtain ⟨hp, he⟩ := (traceOverlapWords_one_iff f).mp hf
  exact (traceOverlapWords_two_iff _).mpr ⟨tracePairReverse_isPair f hp, he⟩

theorem tracePairReverse_mem_one_of_mem_two (f : Fin 6 → V)
    (hf : f ∈ traceOverlapWords G 2) : tracePairReverse f ∈ traceOverlapWords G 1 := by
  obtain ⟨hp, he⟩ := (traceOverlapWords_two_iff f).mp hf
  exact (traceOverlapWords_one_iff _).mpr ⟨tracePairReverse_isPair f hp, he⟩

theorem tracePairReverse_mem_four_of_mem_three (f : Fin 6 → V)
    (hf : f ∈ traceOverlapWords G 3) : tracePairReverse f ∈ traceOverlapWords G 4 := by
  obtain ⟨hp, he, hn⟩ := (traceOverlapWords_three_iff f).mp hf
  exact (traceOverlapWords_four_iff _).mpr ⟨tracePairReverse_isPair f hp, he, hn⟩

theorem tracePairReverse_mem_three_of_mem_four (f : Fin 6 → V)
    (hf : f ∈ traceOverlapWords G 4) : tracePairReverse f ∈ traceOverlapWords G 3 := by
  obtain ⟨hp, he, hn⟩ := (traceOverlapWords_four_iff f).mp hf
  exact (traceOverlapWords_three_iff _).mpr ⟨tracePairReverse_isPair f hp, he, hn⟩

theorem trace_overlap_one_card_eq_two :
    (traceOverlapWords G 1).card = (traceOverlapWords G 2).card := by
  classical
  apply Finset.card_bij (fun f _ => tracePairReverse f)
  · intro f hf
    exact tracePairReverse_mem_two_of_mem_one f hf
  · intro f _ g _ he
    have h := congrArg tracePairReverse he
    simpa only [tracePairReverse_involutive] using h
  · intro g hg
    exact ⟨tracePairReverse g, tracePairReverse_mem_one_of_mem_two g hg,
      tracePairReverse_involutive g⟩

theorem trace_overlap_three_card_eq_four :
    (traceOverlapWords G 3).card = (traceOverlapWords G 4).card := by
  classical
  apply Finset.card_bij (fun f _ => tracePairReverse f)
  · intro f hf
    exact tracePairReverse_mem_four_of_mem_three f hf
  · intro f _ g _ he
    have h := congrArg tracePairReverse he
    simpa only [tracePairReverse_involutive] using h
  · intro g hg
    exact ⟨tracePairReverse g, tracePairReverse_mem_three_of_mem_four g hg,
      tracePairReverse_involutive g⟩

end TaskH.Six

#print axioms TaskH.Six.traceThreePath_reverse
#print axioms TaskH.Six.tracePairReverse_involutive
#print axioms TaskH.Six.tracePairReverse_isPair
#print axioms TaskH.Six.tracePairReverse_mem_two_of_mem_one
#print axioms TaskH.Six.tracePairReverse_mem_one_of_mem_two
#print axioms TaskH.Six.tracePairReverse_mem_four_of_mem_three
#print axioms TaskH.Six.tracePairReverse_mem_three_of_mem_four
#print axioms TaskH.Six.trace_overlap_one_card_eq_two
#print axioms TaskH.Six.trace_overlap_three_card_eq_four
