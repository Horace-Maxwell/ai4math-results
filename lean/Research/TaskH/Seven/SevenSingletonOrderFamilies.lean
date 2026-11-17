import Research.TaskH.Seven.SingletonClique
import Research.TaskH.Seven.SevenIncidence

/-! Fixed-singleton following families on actual unoriented cycle edge sets.
The missing-color statement excludes every point of the old color class. -/

set_option autoImplicit false
universe u
namespace TaskH.Seven
open SimpleGraph _root_.TaskH.Challenge
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def singletonOrderCycleFinset (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) : Finset (Finset (Sym2 V)) := by
  classical
  exact (cycleFinset G).filter (fun s => ∃ π : Equiv.Perm (Fin 7),
    π ∈ basedCycleOrders (G := G) (singletonEdgeColoring v c i) v s)

theorem mem_singletonOrderCycleFinset (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) (s : Finset (Sym2 V)) :
    s ∈ singletonOrderCycleFinset v c i ↔ s ∈ cycleFinset G ∧
      ∃ π : Equiv.Perm (Fin 7),
        π ∈ basedCycleOrders (G := G) (singletonEdgeColoring v c i) v s := by
  classical
  simp only [singletonOrderCycleFinset, Finset.mem_filter]

theorem singletonOrderCycleFinset_card_ge (hcrit : IsCriticalPlus 7 G)
    (hs : ShortSevenCycles G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) :
    360 ≤ (singletonOrderCycleFinset v c i).card := by
  classical
  let A : Finset (Equiv.Perm (Fin 7)) := Finset.univ
  let C := singletonOrderCycleFinset v c i
  let R : Equiv.Perm (Fin 7) → Finset (Sym2 V) → Prop :=
    fun π s => π ∈ basedCycleOrders (G := G) (singletonEdgeColoring v c i) v s
  have hA : A.card = 5040 := by norm_num [A, Fintype.card_perm]
  have hrow : ∀ π ∈ A, 1 ≤ (C.filter (R π)).card := by
    intro π _hπ
    obtain ⟨p, hp, hlen, hf, _hout⟩ := singleton_through_ordered_cycle hcrit hs v c i π
    have hπ : R π p.edges.toFinset :=
      (mem_basedCycleOrders _ v p.edges.toFinset π).mpr
        ⟨p, hp, hlen, p.coe_edges_toFinset.symm, hf⟩
    have hm : p.edges.toFinset ∈ C.filter (R π) := by
      apply Finset.mem_filter.mpr
      refine ⟨(mem_singletonOrderCycleFinset v c i _).mpr ⟨?_, π, hπ⟩, hπ⟩
      apply (mem_cycleFinset _).mpr
      apply Basics.mem_modCycleEdgeSets_iff.mpr
      exact ⟨v, p, hp, rfl, by simpa only [hlen] using (dvd_refl 7)⟩
    exact Finset.card_pos.mpr ⟨p.edges.toFinset, hm⟩
  have hcol : ∀ s ∈ C, (A.filter (fun π => R π s)).card ≤ 14 := by
    intro s _hs
    have he : A.filter (fun π => R π s) =
        basedCycleOrders (G := G) (singletonEdgeColoring v c i) v s := by
      ext π
      simp only [A, R, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact basedCycleOrders_card_le_fourteen _ v s
  have hd : (∑ π ∈ A, (C.filter (R π)).card) =
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := by
    convert FiniteBudget.relation_double_count A C R using 1 <;>
      apply Finset.sum_congr rfl
    all_goals
      intro z _
      congr 1
      ext w
      simp only [Finset.mem_filter]
  have hlo : A.card ≤ ∑ π ∈ A, (C.filter (R π)).card := by
    calc
      A.card = ∑ _π ∈ A, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhi : (∑ s ∈ C, (A.filter (fun π => R π s)).card) ≤ C.card * 14 := by
    calc
      _ ≤ ∑ _s ∈ C, 14 := Finset.sum_le_sum hcol
      _ = _ := by simp
  have hmid : (∑ π ∈ A, (C.filter (R π)).card) ≤
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := le_of_eq hd
  have htotal : (∑ π ∈ A, (C.filter (R π)).card) ≤ C.card * 14 :=
    Nat.le_trans hmid hhi
  have hh : 5040 ≤ C.card * 14 := by
    rw [hA] at hlo
    exact Nat.le_trans hlo htotal
  change 360 ≤ C.card
  omega

theorem singletonOrderCycle_contains_root (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) {s : Finset (Sym2 V)}
    (hm : s ∈ singletonOrderCycleFinset v c i) : CycleContains s v := by
  obtain ⟨_hs, π, hπ⟩ := (mem_singletonOrderCycleFinset v c i s).mp hm
  obtain ⟨p, hp, _hlen, hset, _hf⟩ := (mem_basedCycleOrders _ v s π).mp hπ
  have he : p.edges.toFinset = s := Finset.coe_injective (p.coe_edges_toFinset.trans hset)
  rw [← he]
  exact (TaskH.cycleContains_edges_toFinset_iff p hp.not_nil v).mpr p.start_mem_support

theorem singletonOrderCycle_missing_entire_class (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i : ↥(singletonNeighborColors v c)) {s : Finset (Sym2 V)}
    (hm : s ∈ singletonOrderCycleFinset v c i)
    (z : {x : V // x ≠ v}) (hz : c z = i.val) : ¬ CycleContains s z.val := by
  obtain ⟨_hs, π, hπ⟩ := (mem_singletonOrderCycleFinset v c i s).mp hm
  obtain ⟨p, hp, hlen, hset, hf⟩ := (mem_basedCycleOrders _ v s π).mp hπ
  have he : p.edges.toFinset = s := Finset.coe_injective (p.coe_edges_toFinset.trans hset)
  intro hhit
  have hzp : z.val ∈ p.support := by
    apply (TaskH.cycleContains_edges_toFinset_iff p hp.not_nil z.val).mp
    simpa only [he] using hhit
  exact singleton_cycle_missing_color v c i π p hlen hf z hzp hz

theorem singletonOrderCycle_contains_other_singleton (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i j : ↥(singletonNeighborColors v c)) (hij : i ≠ j)
    {s : Finset (Sym2 V)} (hm : s ∈ singletonOrderCycleFinset v c i) :
    CycleContains s (singletonNeighbor v c j).val := by
  obtain ⟨_hs, π, hπ⟩ := (mem_singletonOrderCycleFinset v c i s).mp hm
  obtain ⟨p, hp, hlen, hset, hf⟩ := (mem_basedCycleOrders _ v s π).mp hπ
  have he : p.edges.toFinset = s := Finset.coe_injective (p.coe_edges_toFinset.trans hset)
  rw [← he]
  exact (TaskH.cycleContains_edges_toFinset_iff p hp.not_nil _).mpr
    (singleton_cycle_contains_other_neighbor hr v c i j hij π p hp hlen hf)

theorem singleton_neighbor_cycleDegree_ge_seven_hundred_twenty
    (hcrit : IsCriticalPlus 7 G) (hs : ShortSevenCycles G) (hr : RainbowSevenCycles G)
    (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin 7))
    (i j : ↥(singletonNeighborColors v c)) (hij : i ≠ j) :
    720 ≤ cycleDegree G (singletonNeighbor v c j).val := by
  classical
  let F := singletonOrderCycleFinset v c i
  let A := throughAvoidFinset G (singletonNeighbor v c j).val v
  have hF : 360 ≤ F.card := singletonOrderCycleFinset_card_ge hcrit hs v c i
  have hA : 360 ≤ A.card := by
    rw [throughAvoidFinset_card]
    exact critical_edge_three_hundred_sixty_modCyclesThroughAvoid hcrit hs
      (singletonNeighbor v c j).property.symm
  have hdis : Disjoint F A := by
    apply Finset.disjoint_left.mpr
    intro s hsF hsA
    have hh : ¬ CycleContains s v := (Finset.mem_filter.mp hsA).2.2
    exact hh (singletonOrderCycle_contains_root v c i hsF)
  have hsub : F ∪ A ⊆ throughFinset G (singletonNeighbor v c j).val := by
    intro s hm
    apply (mem_throughFinset s _).mpr
    rcases Finset.mem_union.mp hm with hF | hA
    · exact ⟨(mem_cycleFinset s).mp ((mem_singletonOrderCycleFinset v c i s).mp hF).1,
        singletonOrderCycle_contains_other_singleton hr v c i j hij hF⟩
    · have hh := Finset.mem_filter.mp hA
      exact ⟨(mem_cycleFinset s).mp hh.1, hh.2.1⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hh
  change F.card + A.card ≤ cycleDegree G (singletonNeighbor v c j).val at hh
  omega

end TaskH.Seven
#print axioms TaskH.Seven.singletonOrderCycleFinset
#print axioms TaskH.Seven.mem_singletonOrderCycleFinset
#print axioms TaskH.Seven.singletonOrderCycleFinset_card_ge
#print axioms TaskH.Seven.singletonOrderCycle_contains_root
#print axioms TaskH.Seven.singletonOrderCycle_missing_entire_class
#print axioms TaskH.Seven.singletonOrderCycle_contains_other_singleton
#print axioms TaskH.Seven.singleton_neighbor_cycleDegree_ge_seven_hundred_twenty
