import Research.TaskH.Seven.SevenIncidence
import Research.TaskH.Seven.SevenAttachment

/-! The forward neighbor-cycle double count on actual counted edge sets. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem finSeven_next_prev_ne (i : Fin 7) : i + 1 ≠ i + 6 := by
  revert i
  decide +kernel

theorem finSeven_prev_succ (i : Fin 7) : (i + 6) + 1 = i := by
  revert i
  decide +kernel

open scoped Classical in
theorem two_le_heptagon_neighbors [DecidableRel G.Adj]
    (f : Fin 7 → V) (hf : IsHeptagon G f) (i : Fin 7) :
    2 ≤ ((G.neighborFinset (f i)).filter
      (fun x => CycleContains (heptagonEdges f) x)).card := by
  classical
  have hnext := heptagon_adj_succ hf i
  have hprev : G.Adj (f i) (f (i + 6)) := by
    have hh := (heptagon_adj_succ hf (i + 6)).symm
    simpa only [finSeven_prev_succ] using hh
  have hne : f (i + 1) ≠ f (i + 6) := hf.1.ne (finSeven_next_prev_ne i)
  have hsub : ({f (i + 1), f (i + 6)} : Finset V) ⊆
      (G.neighborFinset (f i)).filter
        (fun x => CycleContains (heptagonEdges f) x) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hnext,
        (cycleContains_heptagonEdges_iff f _).mpr ⟨i + 1, rfl⟩⟩
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hprev,
        (cycleContains_heptagonEdges_iff f _).mpr ⟨i + 6, rfl⟩⟩
  simpa only [Finset.card_pair hne] using Finset.card_le_card hsub

open scoped Classical in
theorem two_le_cycle_neighbors [DecidableRel G.Adj]
    (hs : ShortSevenCycles G) (s : Finset (Sym2 V))
    (hmem : s ∈ ModCycleEdgeSets 7 G) (v : V) (hv : CycleContains s v) :
    2 ≤ ((G.neighborFinset v).filter (fun x => CycleContains s x)).card := by
  classical
  obtain ⟨a, p, hp, he, hk⟩ := Basics.mem_modCycleEdgeSets_iff.mp hmem
  have hl := hs p hp hk
  obtain ⟨f, hf, hfe⟩ := exists_heptagon_of_cycle_length_seven hp hl
  have hvf : CycleContains (heptagonEdges f) v := by simpa only [hfe, he] using hv
  obtain ⟨i, rfl⟩ := (cycleContains_heptagonEdges_iff f v).mp hvf
  simpa only [hfe, he] using two_le_heptagon_neighbors f hf i

theorem forward_neighbor_cycle_budget [DecidableRel G.Adj]
    (hs : ShortSevenCycles G)
    (hE : ∀ {x y : V}, G.Adj x y →
      360 ≤ (TaskH.modCyclesThroughAvoid 7 G x y).ncard) (v : V) :
    360 * G.degree v + 2 * cycleDegree G v ≤ G.degree v * cycleDegree G v := by
  classical
  let B : V → Finset (Finset (Sym2 V)) :=
    fun x => (throughFinset G v).filter (fun s => CycleContains s x)
  have hrow : ∀ x ∈ G.neighborFinset v, 360 + (B x).card ≤ cycleDegree G v := by
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
  have hsum : 360 * G.degree v + (∑ x ∈ G.neighborFinset v, (B x).card) ≤
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

/-- Both incidence inequalities now follow from the actual critical graph,
not from an attachment hypothesis supplied to the main theorem. -/
theorem critical_reverse_neighbor_cycle_budget [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (hn : 9 ≤ Fintype.card V) (hc : modCycleCount 7 G = 2880) (v : V) :
    360 * G.degree v ≤ 4 * (2880 - cycleDegree G v) := by
  apply reverse_neighbor_cycle_budget hc
    (fun {_x _y} hxy => critical_edge_three_hundred_sixty_modCyclesThroughAvoid hcrit hs hxy)
  exact outside_cycle_neighbors_card_le_four hcrit hs hr hn

theorem critical_forward_neighbor_cycle_budget [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (v : V) :
    360 * G.degree v + 2 * cycleDegree G v ≤ G.degree v * cycleDegree G v :=
  forward_neighbor_cycle_budget hs
    (fun {_x _y} hxy => critical_edge_three_hundred_sixty_modCyclesThroughAvoid hcrit hs hxy) v

theorem critical_forward_neighbor_cycle_budget_sub [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (v : V) :
    2 * cycleDegree G v ≤ G.degree v * (cycleDegree G v - 360) := by
  have hh := critical_forward_neighbor_cycle_budget hcrit hs v
  rw [Nat.mul_sub_left_distrib]
  omega

end TaskH.Seven

#print axioms TaskH.Seven.finSeven_next_prev_ne
#print axioms TaskH.Seven.finSeven_prev_succ
#print axioms TaskH.Seven.two_le_heptagon_neighbors
#print axioms TaskH.Seven.two_le_cycle_neighbors
#print axioms TaskH.Seven.forward_neighbor_cycle_budget

#print axioms TaskH.Seven.critical_reverse_neighbor_cycle_budget
#print axioms TaskH.Seven.critical_forward_neighbor_cycle_budget
#print axioms TaskH.Seven.critical_forward_neighbor_cycle_budget_sub
