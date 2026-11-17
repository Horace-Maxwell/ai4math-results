import Research.TaskH.Five.CycleFive

/-!
Finite incidence objects for the original modulo-five cycle edge sets.
Conditional counting lemmas take bounds on these actual graph objects;
the equality proof must derive those bounds before using the lemmas.
-/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def cycleFinset (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  (Basics.modCycleEdgeSets_finite 5 G).toFinset

theorem mem_cycleFinset (s : Finset (Sym2 V)) :
    s ∈ cycleFinset G ↔ s ∈ ModCycleEdgeSets 5 G := by
  classical
  simp [cycleFinset]

theorem cycleFinset_card : (cycleFinset G).card = modCycleCount 5 G := by
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
    s ∈ throughFinset G v ↔ s ∈ ModCycleEdgeSets 5 G ∧ CycleContains s v := by
  classical
  simp [throughFinset, mem_cycleFinset]

theorem mem_avoidingFinset (s : Finset (Sym2 V)) (v : V) :
    s ∈ avoidingFinset G v ↔ s ∈ ModCycleEdgeSets 5 G ∧ ¬ CycleContains s v := by
  classical
  simp [avoidingFinset, mem_cycleFinset]

theorem cycleDegree_eq_ncard (v : V) :
    cycleDegree G v = (TaskH.modCyclesThrough 5 G v).ncard := by
  classical
  have he : TaskH.modCyclesThrough 5 G v =
      ((throughFinset G v : Finset (Finset (Sym2 V))) : Set (Finset (Sym2 V))) := by
    ext s
    exact (mem_throughFinset s v).symm
  rw [he, Set.ncard_coe_finset]
  rfl

theorem throughAvoidFinset_card (v w : V) :
    (throughAvoidFinset G v w).card =
      (TaskH.modCyclesThroughAvoid 5 G v w).ncard := by
  classical
  have he : TaskH.modCyclesThroughAvoid 5 G v w =
      ((throughAvoidFinset G v w : Finset (Finset (Sym2 V))) :
        Set (Finset (Sym2 V))) := by
    ext s
    simp [TaskH.modCyclesThroughAvoid, throughAvoidFinset, mem_cycleFinset]
  rw [he, Set.ncard_coe_finset]

theorem through_add_avoiding (v : V) :
    cycleDegree G v + (avoidingFinset G v).card = modCycleCount 5 G := by
  classical
  change ((cycleFinset G).filter (fun s => CycleContains s v)).card +
    ((cycleFinset G).filter (fun s => ¬ CycleContains s v)).card = _
  rw [Finset.card_filter_add_card_filter_not, cycleFinset_card]

theorem sum_cycleDegree (hs : ShortFiveCycles G) :
    (∑ v : V, cycleDegree G v) = 5 * modCycleCount 5 G := by
  classical
  have he := FiniteBudget.relation_double_count (Finset.univ : Finset V)
    (cycleFinset G) (fun v s => CycleContains s v)
  calc
    (∑ v : V, cycleDegree G v) =
        ∑ s ∈ cycleFinset G,
          ((Finset.univ : Finset V).filter (fun v => CycleContains s v)).card := he
    _ = ∑ _s ∈ cycleFinset G, 5 := by
      apply Finset.sum_congr rfl
      intro s hs'
      change (TaskH.cycleVertices s).card = 5
      exact cycleVertices_card_five_of_mem hs ((mem_cycleFinset s).mp hs')
    _ = 5 * modCycleCount 5 G := by simp [cycleFinset_card, Nat.mul_comm]

theorem sum_cycleDegree_eq_360 (hs : ShortFiveCycles G)
    (hc : modCycleCount 5 G = 72) : (∑ v : V, cycleDegree G v) = 360 := by
  rw [sum_cycleDegree hs, hc]

theorem thirteen_le_cycleDegree [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 5 G)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard) (v : V) :
    13 ≤ cycleDegree G v := by
  classical
  have hd := TaskH.critical_degree_ge hcrit v
  have hpos : 0 < (G.neighborFinset v).card := by
    rw [G.card_neighborFinset_eq_degree]
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hEw := hE hvw
  have hAf : (TaskH.modCyclesThroughAvoid 5 G v w).Finite :=
    (Basics.modCycleEdgeSets_finite 5 G).subset (fun _ hs => hs.1)
  obtain ⟨C, hC⟩ := (Set.ncard_pos hAf).mp (by omega :
    0 < (TaskH.modCyclesThroughAvoid 5 G v w).ncard)
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
  let A := TaskH.modCyclesThroughAvoid 5 G v z
  have hA : A.Finite :=
    (Basics.modCycleEdgeSets_finite 5 G).subset (fun _ hs => hs.1)
  have hnot : C ∉ A := by
    intro hmem
    exact hmem.2.2 hCz
  have hsub : insert C A ⊆ TaskH.modCyclesThrough 5 G v := by
    intro s hmem
    rcases Set.mem_insert_iff.mp hmem with rfl | hmem
    · exact ⟨hC.1, hC.2.1⟩
    · exact ⟨hmem.1, hmem.2.1⟩
  have hle := Set.ncard_le_ncard hsub (TaskH.modCyclesThrough_finite 5 G v)
  rw [Set.ncard_insert_of_notMem hnot hA] at hle
  have hEz : 12 ≤ A.ncard := hE hvz
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
theorem cycleDegree_add_six_degree_le_seventy_two [DecidableRel G.Adj]
    (hc : modCycleCount 5 G = 72)
    (hE : ∀ {x y : V}, G.Adj x y →
      12 ≤ (TaskH.modCyclesThroughAvoid 5 G x y).ncard)
    (hattach : ∀ (s : Finset (Sym2 V)), s ∈ ModCycleEdgeSets 5 G →
      ∀ v : V, ¬ CycleContains s v →
      ((G.neighborFinset v).filter (fun x => CycleContains s x)).card ≤ 2)
    (v : V) : cycleDegree G v + 6 * G.degree v ≤ 72 := by
  classical
  have hl : 12 * G.degree v ≤
      ∑ x ∈ G.neighborFinset v, (throughAvoidFinset G x v).card := by
    calc
      12 * G.degree v = ∑ _x ∈ G.neighborFinset v, 12 := by
        simp [G.card_neighborFinset_eq_degree, Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro x hx
        rw [throughAvoidFinset_card]
        exact hE ((G.mem_neighborFinset v x).mp hx).symm
  rw [avoid_neighbor_double_count] at hl
  have hu : (∑ s ∈ avoidingFinset G v,
      ((G.neighborFinset v).filter (fun x => CycleContains s x)).card) ≤
        2 * (avoidingFinset G v).card := by
    calc
      _ ≤ ∑ _s ∈ avoidingFinset G v, 2 := by
        apply Finset.sum_le_sum
        intro s hs'
        have hmem := (mem_avoidingFinset s v).mp hs'
        exact hattach s hmem.1 v hmem.2
      _ = _ := by simp [Nat.mul_comm]
  have hp := through_add_avoiding (G := G) v
  rw [hc] at hp
  omega

end TaskH.Five

#print axioms TaskH.Five.mem_cycleFinset
#print axioms TaskH.Five.cycleFinset_card
#print axioms TaskH.Five.mem_throughFinset
#print axioms TaskH.Five.mem_avoidingFinset
#print axioms TaskH.Five.cycleDegree_eq_ncard
#print axioms TaskH.Five.throughAvoidFinset_card
#print axioms TaskH.Five.through_add_avoiding
#print axioms TaskH.Five.sum_cycleDegree
#print axioms TaskH.Five.sum_cycleDegree_eq_360
#print axioms TaskH.Five.thirteen_le_cycleDegree
#print axioms TaskH.Five.avoid_neighbor_double_count
#print axioms TaskH.Five.cycleDegree_add_six_degree_le_seventy_two
