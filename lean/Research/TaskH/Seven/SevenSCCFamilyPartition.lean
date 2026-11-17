import Research.TaskH.Seven.SevenSCCFamily
import Research.TaskH.Seven.SevenSCCFamilyOrders

/-! Exact partition of the selected actual following-circle edge sets
over the actual deduplicated successor component vertex sets. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem sccBadCircleFinset_eq_jointCircleFinset (x y : V) :
    sccBadCircleFinset G x y = jointCircleFinset G x y := rfl

noncomputable def componentCircleFinset (G : SimpleGraph V) {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) (Q : Finset V) : Finset (Finset (Sym2 V)) :=
  (orderFollowingCircleFinset G x y c π).filter (fun C => TaskH.cycleVertices C ⊆ Q)

theorem componentCircleFinset_eq_following {x y a : V} (hxy : x ≠ y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) :
    componentCircleFinset G c π
      (successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) a) =
      sccFollowingCircleFinset G c π a := by
  classical
  ext C
  constructor
  · intro hC
    have hglob := (Finset.mem_filter.mp hC).1
    have hsub := (Finset.mem_filter.mp hC).2
    have horders := (Finset.mem_filter.mp hglob).2
    obtain ⟨z, p, hp, hl, hset, hf⟩ := (Finset.mem_filter.mp horders).2
    have hzC : z ∈ TaskH.cycleVertices C := by
      apply (TaskH.mem_cycleVertices C z).mpr
      rw [← hset]
      exact (cycleContains_edges_toFinset_iff p hp.not_nil z).mpr p.start_mem_support
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hglob).1).1,
      z, hsub hzC, p, hp, hl, ?_, hset⟩
    exact (follows_orderedColorCycle_iff p c π).mpr hf
  · intro hC
    obtain ⟨z, _hz, p, hp, hl, hf, hset⟩ := (Finset.mem_filter.mp hC).2
    apply Finset.mem_filter.mpr
    refine ⟨?_, sccFollowingCircleFinset_support_subset c he π hC⟩
    rw [← hset]
    exact mem_orderFollowingCircleFinset_of_cycle hxy c he π p hp hl hf

/-- Every actual following circle belongs to exactly one actual component;
the basepoint supplies the common vertex proving uniqueness. -/
theorem circle_component_fiber_card {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) {C : Finset (Sym2 V)}
    (hC : C ∈ orderFollowingCircleFinset G x y c π) :
    ((successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π)).filter
      (fun Q => TaskH.cycleVertices C ⊆ Q)).card = 1 := by
  classical
  have horders := (Finset.mem_filter.mp hC).2
  obtain ⟨z, p, hp, _hl, hset, hf⟩ := (Finset.mem_filter.mp horders).2
  have hf' := (follows_orderedColorCycle_iff p c π).mpr hf
  let Q := successorComponent (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) z
  have hQ : Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π) :=
    Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
  have hzC : z ∈ TaskH.cycleVertices C := by
    apply (TaskH.mem_cycleVertices C z).mpr
    rw [← hset]
    exact (cycleContains_edges_toFinset_iff p hp.not_nil z).mpr p.start_mem_support
  have hsub : TaskH.cycleVertices C ⊆ Q := by
    intro w hw
    have hwp : w ∈ p.support := by
      apply (cycleContains_edges_toFinset_iff p hp.not_nil w).mp
      rw [hset]
      exact (TaskH.mem_cycleVertices C w).mp hw
    exact following_circle_support_in_component c π he p hf' hwp
  have hfilter :
      (successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π)).filter
        (fun P => TaskH.cycleVertices C ⊆ P) = {Q} := by
    ext P
    constructor
    · intro hP
      have hPm := (Finset.mem_filter.mp hP).1
      have hzP := (Finset.mem_filter.mp hP).2 hzC
      have hzQ : z ∈ Q := successorComponent_self c (orderedColorCycle π) z
      have hPQ : P = Q := by
        by_contra hne
        have hdis := successorComponents_pairwiseDisjoint c (orderedColorCycle π)
          hPm hQ hne
        exact Finset.disjoint_left.mp hdis hzP hzQ
      exact Finset.mem_singleton.mpr hPQ
    · intro hP
      have hPQ := Finset.mem_singleton.mp hP
      subst P
      exact Finset.mem_filter.mpr ⟨hQ, hsub⟩
  rw [hfilter]
  simp

theorem sum_componentCircleFinset_card {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) (he : c x = c y)
    (π : Equiv.Perm (Fin 7)) :
    (∑ Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π),
      (componentCircleFinset G c π Q).card) =
      (orderFollowingCircleFinset G x y c π).card := by
  classical
  have hdouble (A : Finset (Finset V)) (B : Finset (Finset (Sym2 V))) :
      (∑ Q ∈ A, (B.filter (fun C => TaskH.cycleVertices C ⊆ Q)).card) =
        ∑ C ∈ B, (A.filter (fun Q => TaskH.cycleVertices C ⊆ Q)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  let A := successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π)
  let B := orderFollowingCircleFinset G x y c π
  have hcomponent (Q : Finset V) : componentCircleFinset G c π Q =
      B.filter (fun C => TaskH.cycleVertices C ⊆ Q) :=
    Finset.filter_congr_decidable _ _ _
  calc
    _ = ∑ Q ∈ A, (B.filter (fun C => TaskH.cycleVertices C ⊆ Q)).card := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      exact congrArg Finset.card (hcomponent Q)
    _ = ∑ C ∈ B, (A.filter (fun Q => TaskH.cycleVertices C ⊆ Q)).card := hdouble A B
    _ = ∑ _C ∈ B, 1 := by
      apply Finset.sum_congr rfl
      intro C hC
      exact circle_component_fiber_card (G := G) (x := x) (y := y) c he π hC
    _ = B.card := (Finset.card_eq_sum_ones B).symm

theorem equality_componentCircleFinset_cover [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    {x y : V} (hxy : x ≠ y) (hbad : (jointCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7)) {Q : Finset V}
    (hQ : Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π)) :
    Q.card ≤ 6 * (componentCircleFinset G c π Q).card + 1 := by
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hQ
  rw [componentCircleFinset_eq_following hxy c (deletedEdge_coloring_endpoints hcrit c) π]
  apply equality_successorComponent_card_le_six_circleCard_add_one hcrit hc
  rw [sccBadCircleFinset_eq_jointCircleFinset]
  exact hbad

/-- Original equality plus the one remaining internal lower-circle-count
obligation closes order45. This is not an original-looking theorem that
pretends the one-cycle-component exclusion has already been proved. -/
theorem equality_order45_of_component_circle_lower [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    {x y : V} (hxy : x ≠ y) (hbad : (jointCircleFinset G x y).card ≤ 78)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (π : Equiv.Perm (Fin 7))
    (hsmall : (orderFollowingCircleFinset G x y c π).card ≤ 7)
    (hmin : ∀ Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π),
      2 ≤ (componentCircleFinset G c π Q).card) : Fintype.card V ≤ 45 := by
  apply order45_of_finite_component_budgets
    (successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π))
    (fun Q => Q.card) (fun Q => (componentCircleFinset G c π Q).card) (Fintype.card V)
    (sum_successorComponent_card c (orderedColorCycle π))
    (fun Q hQ => equality_componentCircleFinset_cover hcrit hc hxy hbad c π hQ) hmin
  rw [sum_componentCircleFinset_card c (deletedEdge_coloring_endpoints hcrit c) π]
  exact hsmall

/-- All actual finite component data required for the final contradiction
are obtained from the original equality and an order at least46. The
unproved one-circle-component exclusion is deliberately not asserted. -/
theorem equality_exists_small_component_circle_system [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hn : 46 ≤ Fintype.card V) :
    ∃ x y : V, G.Adj x y ∧
      ∃ c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7),
      ∃ π : Equiv.Perm (Fin 7),
        1 ≤ (jointCircleFinset G x y).card ∧ (jointCircleFinset G x y).card ≤ 78 ∧
        (orderFollowingCircleFinset G x y c π).card ≤ 7 ∧
        (∑ Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π),
          (componentCircleFinset G c π Q).card) =
          (orderFollowingCircleFinset G x y c π).card ∧
        ∀ Q ∈ successorComponents (G.deleteEdges {s(x, y)}) c (orderedColorCycle π),
          Q.card ≤ 6 * (componentCircleFinset G c π Q).card + 1 := by
  obtain ⟨x, y, hxy, _hx, hpos, hbad⟩ := equality_exists_light_circle_edge hcrit hc hn
  obtain ⟨c⟩ := critical_colorable_deletedEdge hcrit hxy
  obtain ⟨π, hsmall⟩ := exists_orderFollowingCircleFinset_card_le_seven hc hpos c
  refine ⟨x, y, hxy, c, π, hpos, hbad, hsmall, ?_, ?_⟩
  · exact sum_componentCircleFinset_card c (deletedEdge_coloring_endpoints hcrit c) π
  · intro Q hQ
    exact equality_componentCircleFinset_cover hcrit hc hxy.ne hbad c π hQ

end TaskH.Seven

#print axioms TaskH.Seven.sccBadCircleFinset_eq_jointCircleFinset
#print axioms TaskH.Seven.componentCircleFinset
#print axioms TaskH.Seven.componentCircleFinset_eq_following
#print axioms TaskH.Seven.circle_component_fiber_card
#print axioms TaskH.Seven.sum_componentCircleFinset_card
#print axioms TaskH.Seven.equality_componentCircleFinset_cover
#print axioms TaskH.Seven.equality_order45_of_component_circle_lower
#print axioms TaskH.Seven.equality_exists_small_component_circle_system
