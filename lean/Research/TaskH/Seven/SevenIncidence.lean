import Research.TaskH.Seven.CycleSeven
import Research.TaskH.Seven.EdgeCyclesCount

/-!
Finite incidence objects for the original modulo-seven cycle edge sets.
Conditional counting lemmas take bounds on these actual graph objects;
the equality proof must derive those bounds before using the lemmas.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def cycleFinset (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  (Basics.modCycleEdgeSets_finite 7 G).toFinset

theorem mem_cycleFinset (s : Finset (Sym2 V)) :
    s ∈ cycleFinset G ↔ s ∈ ModCycleEdgeSets 7 G := by
  classical
  simp [cycleFinset]

theorem cycleFinset_card : (cycleFinset G).card = modCycleCount 7 G := by
  rw [cycleFinset, modCycleCount, Set.ncard_eq_toFinset_card]

noncomputable def throughFinset (G : SimpleGraph V) (v : V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (cycleFinset G).filter (fun s => CycleContains s v)

noncomputable def avoidingFinset (G : SimpleGraph V) (v : V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (cycleFinset G).filter (fun s => ¬ CycleContains s v)

noncomputable def throughAvoidFinset (G : SimpleGraph V) (v w : V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (cycleFinset G).filter (fun s => CycleContains s v ∧ ¬ CycleContains s w)

noncomputable def cycleDegree (G : SimpleGraph V) (v : V) : ℕ :=
  (throughFinset G v).card

theorem mem_throughFinset (s : Finset (Sym2 V)) (v : V) :
    s ∈ throughFinset G v ↔ s ∈ ModCycleEdgeSets 7 G ∧ CycleContains s v := by
  classical
  simp [throughFinset, mem_cycleFinset]

theorem mem_avoidingFinset (s : Finset (Sym2 V)) (v : V) :
    s ∈ avoidingFinset G v ↔ s ∈ ModCycleEdgeSets 7 G ∧ ¬ CycleContains s v := by
  classical
  simp [avoidingFinset, mem_cycleFinset]

theorem cycleDegree_eq_ncard (v : V) :
    cycleDegree G v = (TaskH.modCyclesThrough 7 G v).ncard := by
  classical
  have he : TaskH.modCyclesThrough 7 G v =
      ((throughFinset G v : Finset (Finset (Sym2 V))) : Set (Finset (Sym2 V))) := by
    ext s
    exact (mem_throughFinset s v).symm
  rw [he, Set.ncard_coe_finset]
  rfl

theorem throughAvoidFinset_card (v w : V) :
    (throughAvoidFinset G v w).card =
      (TaskH.modCyclesThroughAvoid 7 G v w).ncard := by
  classical
  have he : TaskH.modCyclesThroughAvoid 7 G v w =
      ((throughAvoidFinset G v w : Finset (Finset (Sym2 V))) :
        Set (Finset (Sym2 V))) := by
    ext s
    simp [TaskH.modCyclesThroughAvoid, throughAvoidFinset, mem_cycleFinset]
  rw [he, Set.ncard_coe_finset]

theorem through_add_avoiding (v : V) :
    cycleDegree G v + (avoidingFinset G v).card = modCycleCount 7 G := by
  classical
  change ((cycleFinset G).filter (fun s => CycleContains s v)).card +
    ((cycleFinset G).filter (fun s => ¬ CycleContains s v)).card = _
  rw [Finset.card_filter_add_card_filter_not, cycleFinset_card]

theorem sum_cycleDegree (hs : ShortSevenCycles G) :
    (∑ v : V, cycleDegree G v) = 7 * modCycleCount 7 G := by
  classical
  have he := FiniteBudget.relation_double_count (Finset.univ : Finset V)
    (cycleFinset G) (fun v s => CycleContains s v)
  calc
    (∑ v : V, cycleDegree G v) =
        ∑ s ∈ cycleFinset G,
          ((Finset.univ : Finset V).filter (fun v => CycleContains s v)).card := he
    _ = ∑ _s ∈ cycleFinset G, 7 := by
      apply Finset.sum_congr rfl
      intro s hs'
      change (TaskH.cycleVertices s).card = 7
      exact cycleVertices_card_seven_of_mem hs ((mem_cycleFinset s).mp hs')
    _ = 7 * modCycleCount 7 G := by simp [cycleFinset_card, Nat.mul_comm]

theorem sum_cycleDegree_eq_20160 (hs : ShortSevenCycles G)
    (hc : modCycleCount 7 G = 2880) : (∑ v : V, cycleDegree G v) = 20160 := by
  rw [sum_cycleDegree hs, hc]

theorem three_hundred_sixty_one_le_cycleDegree [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G)
    (hE : ∀ {x y : V}, G.Adj x y →
      360 ≤ (TaskH.modCyclesThroughAvoid 7 G x y).ncard) (v : V) :
    361 ≤ cycleDegree G v := by
  classical
  have hd := TaskH.critical_degree_ge hcrit v
  have hpos : 0 < (G.neighborFinset v).card := by
    rw [G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hEw := hE hvw
  have hAf : (TaskH.modCyclesThroughAvoid 7 G v w).Finite :=
    (Basics.modCycleEdgeSets_finite 7 G).subset (fun _ hs => hs.1)
  obtain ⟨C, hC⟩ := (Set.ncard_pos hAf).mp (by omega :
    0 < (TaskH.modCyclesThroughAvoid 7 G v w).ncard)
  obtain ⟨a, p, hp, he, _⟩ := Basics.mem_modCycleEdgeSets_iff.mp hC.1
  have hvp : v ∈ p.support := by
    apply (TaskH.cycleContains_edges_toFinset_iff p hp.not_nil v).mp
    simpa only [he] using hC.2.1
  let q : G.Walk v v := p.rotate v hvp
  have hq : q.IsCycle := (Walk.isCycle_rotate hvp).mpr hp
  have hqe : q.edges.toFinset = C := (Basics.rotate_edges_toFinset p v hvp).trans he
  let z : V := q.snd
  have hvz : G.Adj v z := q.adj_snd hq.not_nil
  have hCz : CycleContains C z := by
    rw [← hqe]
    exact (TaskH.cycleContains_edges_toFinset_iff q hq.not_nil z).mpr
      (q.getVert_mem_support 1)
  let A := TaskH.modCyclesThroughAvoid 7 G v z
  have hA : A.Finite :=
    (Basics.modCycleEdgeSets_finite 7 G).subset (fun _ hs => hs.1)
  have hnot : C ∉ A := by
    intro hmem
    exact hmem.2.2 hCz
  have hsub : insert C A ⊆ TaskH.modCyclesThrough 7 G v := by
    intro s hmem
    rcases Set.mem_insert_iff.mp hmem with rfl | hmem
    · exact ⟨hC.1, hC.2.1⟩
    · exact ⟨hmem.1, hmem.2.1⟩
  have hle := Set.ncard_le_ncard hsub (TaskH.modCyclesThrough_finite 7 G v)
  rw [Set.ncard_insert_of_notMem hnot hA] at hle
  have hEz : 360 ≤ A.ncard := hE hvz
  rw [cycleDegree_eq_ncard]
  omega

open scoped Classical in
theorem avoid_neighbor_double_count [DecidableRel G.Adj] (v : V) :
    (∑ x ∈ G.neighborFinset v, (throughAvoidFinset G x v).card) =
      ∑ s ∈ avoidingFinset G v,
        ((G.neighborFinset v).filter (fun x => CycleContains s x)).card := by
  classical
  calc
    (∑ x ∈ G.neighborFinset v, (throughAvoidFinset G x v).card) =
        ∑ x ∈ G.neighborFinset v,
          ((avoidingFinset G v).filter (fun s => CycleContains s x)).card := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ext s
      simp only [throughAvoidFinset, avoidingFinset, Finset.mem_filter]
      tauto
    _ = _ := FiniteBudget.relation_double_count (G.neighborFinset v)
      (avoidingFinset G v) (fun x s => CycleContains s x)

open scoped Classical in
/-- The reverse neighbor-cycle double count, stated on actual graph objects.
The outside-neighbor bound must be proved before this interface is used. -/
theorem reverse_neighbor_cycle_budget [DecidableRel G.Adj]
    (hc : modCycleCount 7 G = 2880)
    (hE : ∀ {x y : V}, G.Adj x y →
      360 ≤ (TaskH.modCyclesThroughAvoid 7 G x y).ncard)
    (hattach : ∀ (s : Finset (Sym2 V)), s ∈ ModCycleEdgeSets 7 G →
      ∀ v : V, ¬ CycleContains s v →
      ((G.neighborFinset v).filter (fun x => CycleContains s x)).card ≤ 4)
    (v : V) : 360 * G.degree v ≤ 4 * (2880 - cycleDegree G v) := by
  classical
  have hl : 360 * G.degree v ≤
      ∑ x ∈ G.neighborFinset v, (throughAvoidFinset G x v).card := by
    calc
      360 * G.degree v = ∑ _x ∈ G.neighborFinset v, 360 := by
        simp [G.card_neighborFinset_eq_degree, Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        rw [throughAvoidFinset_card]
        exact hE ((G.mem_neighborFinset v x).mp hx).symm
  rw [avoid_neighbor_double_count] at hl
  have hu : (∑ s ∈ avoidingFinset G v,
      ((G.neighborFinset v).filter (fun x => CycleContains s x)).card) ≤
        4 * (avoidingFinset G v).card := by
    calc
      _ ≤ ∑ _s ∈ avoidingFinset G v, 4 := by
        apply Finset.sum_le_sum
        intro s hs'
        have hmem := (mem_avoidingFinset s v).mp hs'
        exact hattach s hmem.1 v hmem.2
      _ = _ := by simp [Nat.mul_comm]
  have hp := through_add_avoiding (G := G) v
  rw [hc] at hp
  omega

theorem critical_three_hundred_sixty_one_le_cycleDegree [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (v : V) :
    361 ≤ cycleDegree G v :=
  three_hundred_sixty_one_le_cycleDegree hcrit
    (fun {_x _y} hxy => critical_edge_three_hundred_sixty_modCyclesThroughAvoid hcrit hs hxy) v

end TaskH.Seven

#print axioms TaskH.Seven.cycleFinset
#print axioms TaskH.Seven.mem_cycleFinset
#print axioms TaskH.Seven.cycleFinset_card
#print axioms TaskH.Seven.throughFinset
#print axioms TaskH.Seven.avoidingFinset
#print axioms TaskH.Seven.throughAvoidFinset
#print axioms TaskH.Seven.cycleDegree
#print axioms TaskH.Seven.mem_throughFinset
#print axioms TaskH.Seven.mem_avoidingFinset
#print axioms TaskH.Seven.cycleDegree_eq_ncard
#print axioms TaskH.Seven.throughAvoidFinset_card
#print axioms TaskH.Seven.through_add_avoiding
#print axioms TaskH.Seven.sum_cycleDegree
#print axioms TaskH.Seven.sum_cycleDegree_eq_20160
#print axioms TaskH.Seven.three_hundred_sixty_one_le_cycleDegree
#print axioms TaskH.Seven.avoid_neighbor_double_count
#print axioms TaskH.Seven.reverse_neighbor_cycle_budget
#print axioms TaskH.Seven.critical_three_hundred_sixty_one_le_cycleDegree
