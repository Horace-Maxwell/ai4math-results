import Research.TaskH.Seven.SevenJoint
import Research.TaskH.Seven.EdgeCyclesDistinct
import Research.TaskH.LayerCycleSeparation
import Research.TaskH.FiniteBudget

/-! Actual nonbad circle/order double counting. All5040 permutations are
kept; the proof needs only the fourteen-order column bound, not a quotient
by cyclic rotation/reversal or an exact order multiplicity assumption. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def followingCircleOrders (G : SimpleGraph V) (c : V → Fin 7)
    (C : Finset (Sym2 V)) : Finset (Equiv.Perm (Fin 7)) :=
  Finset.univ.filter (fun π => ∃ z : V, ∃ p : G.Walk z z,
    p.IsCycle ∧ p.length = 7 ∧ p.edges.toFinset = C ∧
      Follows p (fun w => π (c w)) (finRotate 7))

theorem followingCircleOrders_card_le_fourteen (c : V → Fin 7)
    (C : Finset (Sym2 V)) : (followingCircleOrders G c C).card ≤ 14 := by
  classical
  by_cases hn : (followingCircleOrders G c C).Nonempty
  · obtain ⟨π, hπ⟩ := hn
    obtain ⟨z, p, hp, hl, hset, _hf⟩ := (Finset.mem_filter.mp hπ).2
    have hsub : followingCircleOrders G c C ⊆ followingOrders p c ∪ followingOrders p.reverse c := by
      intro ρ hρ
      obtain ⟨w, q, hq, _hql, hqset, hqf⟩ := (Finset.mem_filter.mp hρ).2
      have heq : p.edgeSet = q.edgeSet :=
        CycleOrientation.edgeSet_eq_of_toFinset_eq (hset.trans hqset.symm)
      obtain ⟨hw, hdir⟩ := CycleOrientation.cycle_eq_rotate_or_reverse hp hq heq
      rcases hdir with hdir | hdir
      · apply Finset.mem_union.mpr
        left
        apply (mem_followingOrders p c ρ).mpr
        apply (TaskH.GoodCycles.follows_rotate_iff p w hw
          (fun a => ρ (c a)) (finRotate 7)).mp
        simpa only [hdir] using hqf
      · apply Finset.mem_union.mpr
        right
        apply (mem_followingOrders p.reverse c ρ).mpr
        apply (TaskH.GoodCycles.follows_rotate_reverse_iff p w hw
          (fun a => ρ (c a)) (finRotate 7)).mp
        simpa only [hdir] using hqf
    have hcard := Finset.card_le_card hsub
    have huni := Finset.card_union_le (followingOrders p c) (followingOrders p.reverse c)
    have hpbound := followingOrders_card_le_seven p hl c
    have hrevbound := followingOrders_card_le_seven p.reverse
      (by simpa only [Walk.length_reverse] using hl) c
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

noncomputable def orderFollowingCircleFinset (G : SimpleGraph V) (x y : V)
    (c : V → Fin 7) (π : Equiv.Perm (Fin 7)) : Finset (Finset (Sym2 V)) :=
  (nonbadCircleFinset G x y).filter (fun C => π ∈ followingCircleOrders G c C)

/-- A selected order with at most seven actual nonbad following circle
edge sets exists before any SCC circle-count partition is introduced. -/
theorem exists_orderFollowingCircleFinset_card_le_seven
    (hc : modCycleCount 7 G = 2880) {x y : V}
    (hjoint : 1 ≤ (jointCircleFinset G x y).card) (c : V → Fin 7) :
    ∃ π : Equiv.Perm (Fin 7), (orderFollowingCircleFinset G x y c π).card ≤ 7 := by
  classical
  by_contra hnot
  push Not at hnot
  let A : Finset (Equiv.Perm (Fin 7)) := Finset.univ
  let C := nonbadCircleFinset G x y
  let R : Equiv.Perm (Fin 7) → Finset (Sym2 V) → Prop :=
    fun π s => π ∈ followingCircleOrders G c s
  have hA : A.card = 5040 := by norm_num [A, Fintype.card_perm]
  have hrow : ∀ π ∈ A, 8 ≤ (C.filter (R π)).card := by
    intro π _hπ
    have hπ := hnot π
    change 7 < (C.filter (R π)).card at hπ
    omega
  have hcol : ∀ s ∈ C, (A.filter (fun π => R π s)).card ≤ 14 := by
    intro s _hs
    have he : A.filter (fun π => R π s) = followingCircleOrders G c s := by
      ext π
      simp only [A, R, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he]
    exact followingCircleOrders_card_le_fourteen c s
  have hdouble : (∑ π ∈ A, (C.filter (R π)).card) =
      ∑ s ∈ C, (A.filter (fun π => R π s)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hlo : A.card * 8 ≤ ∑ π ∈ A, (C.filter (R π)).card := by
    calc
      _ = ∑ _π ∈ A, 8 := by simp
      _ ≤ _ := Finset.sum_le_sum hrow
  have hhi : (∑ s ∈ C, (A.filter (fun π => R π s)).card) ≤ C.card * 14 := by
    calc
      _ ≤ ∑ _s ∈ C, 14 := Finset.sum_le_sum hcol
      _ = _ := by simp
  have htotal := joint_add_nonbad (G := G) x y
  rw [hc] at htotal
  have hC : C.card = (nonbadCircleFinset G x y).card := rfl
  omega

theorem follows_circle_not_joint {x y z : V} (hxy : x ≠ y)
    (c : V → Fin 7) (he : c x = c y) (π : Equiv.Perm (Fin 7))
    (p : G.Walk z z) (hp : p.IsCycle) (hl : p.length = 7)
    (hf : Follows p (fun w => π (c w)) (finRotate 7)) :
    ¬ (CycleContains p.edges.toFinset x ∧ CycleContains p.edges.toFinset y) := by
  classical
  have hcases : x = y ∨ x ≠ y := by
    let dec : DecidableEq V := (Fintype.equivFin V).decidableEq
    cases dec x y with
    | isTrue he => exact Or.inl he
    | isFalse hn => exact Or.inr hn
  rcases hcases with hsame | _hne
  · exact (hxy hsame).elim
  rintro ⟨hx, hy⟩
  have hxp := (cycleContains_edges_toFinset_iff p hp.not_nil x).mp hx
  have hyp := (cycleContains_edges_toFinset_iff p hp.not_nil y).mp hy
  have hfrot := (TaskH.GoodCycles.follows_rotate_iff p x hxp
    (fun w => π (c w)) (finRotate 7)).mpr hf
  have hlen : (p.rotate x hxp).length = 7 := by
    simpa only [Walk.length_rotate] using hl
  have havoid := follows_seven_cycle_avoids_same_color (p.rotate x hxp)
    (fun w => π (c w)) hfrot hlen (congrArg π he.symm) hxy
  exact havoid ((Walk.mem_support_rotate_iff p x hxp).mpr hyp)

theorem mem_orderFollowingCircleFinset_of_cycle {x y z : V}
    (hxy : x ≠ y) (c : V → Fin 7) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) (p : G.Walk z z) (hp : p.IsCycle)
    (hl : p.length = 7) (hf : Follows p c (orderedColorCycle π)) :
    p.edges.toFinset ∈ orderFollowingCircleFinset G x y c π := by
  classical
  have hrank := (follows_orderedColorCycle_iff p c π).mp hf
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨(mem_cycleFinset _).mpr ?_, follows_circle_not_joint hxy c he π p hp hl hrank⟩
    apply (Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr
    rw [hl]
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, z, p, hp, hl, rfl, hrank⟩

end TaskH.Seven

#print axioms TaskH.Seven.followingCircleOrders
#print axioms TaskH.Seven.followingCircleOrders_card_le_fourteen
#print axioms TaskH.Seven.orderFollowingCircleFinset
#print axioms TaskH.Seven.exists_orderFollowingCircleFinset_card_le_seven
#print axioms TaskH.Seven.follows_circle_not_joint
#print axioms TaskH.Seven.mem_orderFollowingCircleFinset_of_cycle
