import Research.TaskH.Five.FiveIncidence
import Research.TaskH.Five.FiveAttachmentData

/-! The forward neighbor-cycle double count on actual counted edge sets. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem finFive_next_prev_ne (i : Fin 5) : i + 1 ≠ i + 4 := by
  revert i
  decide +kernel

theorem finFive_prev_succ (i : Fin 5) : (i + 4) + 1 = i := by
  revert i
  decide +kernel

open scoped Classical in
theorem two_le_pentagon_neighbors [DecidableRel G.Adj]
    (f : Fin 5 → V) (hf : IsPentagon G f) (i : Fin 5) :
    2 ≤ ((G.neighborFinset (f i)).filter
      (fun x => CycleContains (pentagonEdges f) x)).card := by
  classical
  have hnext := pentagon_adj_succ hf i
  have hprev : G.Adj (f i) (f (i + 4)) := by
    have hh := (pentagon_adj_succ hf (i + 4)).symm
    simpa only [finFive_prev_succ] using hh
  have hne : f (i + 1) ≠ f (i + 4) := hf.1.ne (finFive_next_prev_ne i)
  have hsub : ({f (i + 1), f (i + 4)} : Finset V) ⊆
      (G.neighborFinset (f i)).filter
        (fun x => CycleContains (pentagonEdges f) x) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hnext,
        (cycleContains_pentagonEdges_iff f _).mpr ⟨i + 1, rfl⟩⟩
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hprev,
        (cycleContains_pentagonEdges_iff f _).mpr ⟨i + 4, rfl⟩⟩
  simpa only [Finset.card_pair hne] using Finset.card_le_card hsub

open scoped Classical in
theorem two_le_cycle_neighbors [DecidableRel G.Adj]
    (hs : ShortFiveCycles G) (s : Finset (Sym2 V))
    (hmem : s ∈ ModCycleEdgeSets 5 G) (v : V) (hv : CycleContains s v) :
    2 ≤ ((G.neighborFinset v).filter (fun x => CycleContains s x)).card := by
  classical
  obtain ⟨a, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  have hl := hs p hp hk
  obtain ⟨f, hf, hfe⟩ := exists_pentagon_of_cycle_length_five hp hl
  have hvf : CycleContains (pentagonEdges f) v := by simpa only [hfe, he] using hv
  obtain ⟨i, rfl⟩ := (cycleContains_pentagonEdges_iff f v).mp hvf
  simpa only [hfe, he] using two_le_pentagon_neighbors f hf i

theorem forward_neighbor_cycle_budget [DecidableRel G.Adj]
    (hs : ShortFiveCycles G)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard) (v : V) :
    12 * G.degree v + 2 * cycleDegree G v ≤ G.degree v * cycleDegree G v := by
  classical
  let B : V → Finset (Finset (Sym2 V)) :=
    fun x => (throughFinset G v).filter (fun s => CycleContains s x)
  have hrow : ∀ x ∈ G.neighborFinset v, 12 + (B x).card ≤ cycleDegree G v := by
    intro x hx
    have he := hE ((G.mem_neighborFinset v x).mp hx)
    rw [← throughAvoidFinset_card] at he
    have havoid : throughAvoidFinset G v x =
        (throughFinset G v).filter (fun s => ¬ CycleContains s x) := by
      ext s
      simp only [throughAvoidFinset, throughFinset, Finset.mem_filter]
      tauto
    rw [havoid] at he
    have hp := Finset.card_filter_add_card_filter_not
      (s := throughFinset G v) (fun s => CycleContains s x)
    change (B x).card +
      ((throughFinset G v).filter (fun s => ¬ CycleContains s x)).card =
        cycleDegree G v at hp
    omega
  have hsum : 12 * G.degree v + (∑ x ∈ G.neighborFinset v, (B x).card) ≤
      G.degree v * cycleDegree G v := by
    have hh := Finset.sum_le_sum hrow
    simpa only [Finset.sum_add_distrib, Finset.sum_const,
      G.card_neighborFinset_eq_degree, Nat.nsmul_eq_mul, Nat.mul_comm] using hh
  have hdouble : (∑ x ∈ G.neighborFinset v, (B x).card) =
      ∑ s ∈ throughFinset G v,
        ((G.neighborFinset v).filter (fun x => CycleContains s x)).card :=
    FiniteBudget.relation_double_count (G.neighborFinset v)
      (throughFinset G v) (fun x s => CycleContains s x)
  have hl : 2 * cycleDegree G v ≤
      ∑ s ∈ throughFinset G v,
        ((G.neighborFinset v).filter (fun x => CycleContains s x)).card := by
    calc
      _ = ∑ _s ∈ throughFinset G v, 2 := by simp [cycleDegree, Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs'
        have hm := (mem_throughFinset s v).mp hs'
        exact two_le_cycle_neighbors hs s hm.1 v hm.2
  rw [hdouble] at hsum
  omega

end TaskH.Five

#print axioms TaskH.Five.finFive_next_prev_ne
#print axioms TaskH.Five.finFive_prev_succ
#print axioms TaskH.Five.two_le_pentagon_neighbors
#print axioms TaskH.Five.two_le_cycle_neighbors
#print axioms TaskH.Five.forward_neighbor_cycle_budget
