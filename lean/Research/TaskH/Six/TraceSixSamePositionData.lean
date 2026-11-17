import Research.TaskH.Six.TraceSixCommonNeighbors
import Research.TaskH.Six.TraceSixPairReversal

/-!
Actual same-first-position pairs have the form `(u,a,b,v,d,a)`.  Their
different internal vertices `b,d` are actual common neighbors of `a,v`;
their permitted roots are the original neighbors of `a` except `v,b,d`.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

def traceSamePositionWord (u a b v d : V) : Fin 6 → V := ![u, a, b, v, d, a]

variable [Fintype V]

noncomputable def traceSamePositionFiber (G : SimpleGraph V) (a v : V) :
    Finset (Fin 6 → V) := by
  classical
  exact (traceOverlapWords G 1).filter (fun f => (f 1, f 3) = (a, v))

theorem mem_traceSamePositionFiber_iff (a v : V) (f : Fin 6 → V) :
    f ∈ traceSamePositionFiber G a v ↔
      f ∈ traceOverlapWords G 1 ∧ (f 1, f 3) = (a, v) := by
  classical
  simp [traceSamePositionFiber]

theorem traceSamePositionFiber_self (a : V) :
    traceSamePositionFiber G a a = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro f hf
  obtain ⟨hfm, he⟩ := (mem_traceSamePositionFiber_iff a a f).mp hf
  have hp := ((traceOverlapWords_one_iff f).mp hfm).1
  have hn := ((traceThreeWord_injective_iff _ _ _ _).mp hp.1.1).2.2.2.2.1
  exact hn ((congrArg Prod.fst he).trans (congrArg Prod.snd he).symm)

variable [DecidableRel G.Adj]

noncomputable def traceSamePositionRoots (G : SimpleGraph V)
    [DecidableRel G.Adj] (a v b d : V) : Finset V := by
  classical
  exact (((G.neighborFinset a).erase v).erase b).erase d

theorem mem_traceSamePositionRoots_iff (a v b d u : V) :
    u ∈ traceSamePositionRoots G a v b d ↔
      G.Adj a u ∧ u ≠ v ∧ u ≠ b ∧ u ≠ d := by
  classical
  simp only [traceSamePositionRoots, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
  tauto

theorem traceSamePositionRoots_card (a v b d : V)
    (hq : (b, d) ∈ (traceCommonNeighbors G a v).offDiag) :
    (traceSamePositionRoots G a v b d).card =
      G.degree a - 2 - (if G.Adj a v then 1 else 0) := by
  classical
  obtain ⟨hb, hd, hbd⟩ := Finset.mem_offDiag.mp hq
  obtain ⟨hab, hvb⟩ := (mem_traceCommonNeighbors_iff a v b).mp hb
  obtain ⟨had, hvd⟩ := (mem_traceCommonNeighbors_iff a v d).mp hd
  have hb0 : b ∈ (G.neighborFinset a).erase v :=
    Finset.mem_erase.mpr ⟨hvb.ne.symm, (G.mem_neighborFinset a b).mpr hab⟩
  have hd0 : d ∈ ((G.neighborFinset a).erase v).erase b :=
    Finset.mem_erase.mpr ⟨hbd.symm,
      Finset.mem_erase.mpr ⟨hvd.ne.symm, (G.mem_neighborFinset a d).mpr had⟩⟩
  rw [traceSamePositionRoots, Finset.card_erase_of_mem hd0,
    Finset.card_erase_of_mem hb0]
  by_cases hav : G.Adj a v
  · rw [Finset.card_erase_of_mem ((G.mem_neighborFinset a v).mpr hav),
      G.card_neighborFinset_eq_degree a, ite_eq_left hav]
    omega
  · have hv : v ∉ G.neighborFinset a := by
      simpa only [SimpleGraph.mem_neighborFinset] using hav
    rw [Finset.erase_eq_of_notMem hv, G.card_neighborFinset_eq_degree a,
      ite_eq_right hav]
    omega

theorem traceSamePositionWord_mem_one (a v b d u : V) (hav : a ≠ v)
    (hq : (b, d) ∈ (traceCommonNeighbors G a v).offDiag)
    (hu : u ∈ traceSamePositionRoots G a v b d) :
    traceSamePositionWord u a b v d ∈ traceOverlapWords G 1 := by
  obtain ⟨hb, hd, hbd⟩ := Finset.mem_offDiag.mp hq
  obtain ⟨hab, hvb⟩ := (mem_traceCommonNeighbors_iff a v b).mp hb
  obtain ⟨had, hvd⟩ := (mem_traceCommonNeighbors_iff a v d).mp hd
  obtain ⟨hau, huv, hub, hud⟩ := (mem_traceSamePositionRoots_iff a v b d u).mp hu
  have hp : IsTracePathPair G (traceSamePositionWord u a b v d) := by
    refine ⟨⟨(traceThreeWord_injective_iff u a b v).mpr ?_,
      hau.symm, hab, hvb.symm⟩,
      ⟨(traceThreeWord_injective_iff u a d v).mpr ?_, hau.symm, had, hvd.symm⟩, ?_⟩
    · exact ⟨hau.ne.symm, hub, huv, hab.ne, hav, hvb.ne.symm⟩
    · exact ⟨hau.ne.symm, hud, huv, had.ne, hav, hvd.ne.symm⟩
    · intro he
      exact hbd (congrArg Prod.snd he)
  exact (traceOverlapWords_one_iff _).mpr ⟨hp, rfl⟩

noncomputable def traceSamePositionBudget (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ := by
  classical
  exact ∑ a : V, ∑ v : V, if a ≠ v then
    (G.degree a - 2 - (if G.Adj a v then 1 else 0)) *
      (traceCommonNeighbors G a v).card.choose 2 else 0

end TaskH.Six

#print axioms TaskH.Six.mem_traceSamePositionFiber_iff
#print axioms TaskH.Six.traceSamePositionFiber_self
#print axioms TaskH.Six.mem_traceSamePositionRoots_iff
#print axioms TaskH.Six.traceSamePositionRoots_card
#print axioms TaskH.Six.traceSamePositionWord_mem_one
