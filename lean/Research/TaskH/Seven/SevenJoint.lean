import Research.TaskH.Seven.SevenEqualityBasics

/-! Actual joint/nonbad original-circle families and the actual light
circle edge required by the direct order45 proof. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph Challenge
open scoped Classical

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def jointCircleFinset (G : SimpleGraph V) (x y : V) :
    Finset (Finset (Sym2 V)) :=
  (cycleFinset G).filter (fun C => CycleContains C x ∧ CycleContains C y)

noncomputable def nonbadCircleFinset (G : SimpleGraph V) (x y : V) :
    Finset (Finset (Sym2 V)) :=
  (cycleFinset G).filter (fun C => ¬ (CycleContains C x ∧ CycleContains C y))

theorem joint_add_nonbad (x y : V) :
    (jointCircleFinset G x y).card + (nonbadCircleFinset G x y).card =
      modCycleCount 7 G := by
  classical
  change ((cycleFinset G).filter (fun C => CycleContains C x ∧ CycleContains C y)).card +
    ((cycleFinset G).filter (fun C => ¬ (CycleContains C x ∧ CycleContains C y))).card = _
  rw [Finset.card_filter_add_card_filter_not, cycleFinset_card]

theorem joint_add_throughAvoid (x y : V) :
    (jointCircleFinset G x y).card + (throughAvoidFinset G x y).card = cycleDegree G x := by
  classical
  have hyes : (throughFinset G x).filter (fun C => CycleContains C y) =
      jointCircleFinset G x y := by
    ext C
    simp [throughFinset, jointCircleFinset, and_assoc]
  have hno : (throughFinset G x).filter (fun C => ¬ CycleContains C y) =
      throughAvoidFinset G x y := by
    ext C
    simp [throughFinset, throughAvoidFinset, and_assoc]
  rw [← hyes, ← hno]
  exact Finset.card_filter_add_card_filter_not (fun C => CycleContains C y)

theorem exists_cycleDegree_le_438
    (hsum : (∑ x : V, cycleDegree G x) = 20160)
    (hn : 46 ≤ Fintype.card V) : ∃ x : V, cycleDegree G x ≤ 438 := by
  classical
  by_contra hnot
  push Not at hnot
  have hlow : Fintype.card V * 439 ≤ ∑ x : V, cycleDegree G x := by
    calc
      _ = ∑ _x : V, 439 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x _ => by have hx := hnot x; omega)
  rw [hsum] at hlow
  omega

/-- The selected pair lies on a genuine original circle edge. Joint
counts contain both vertices, whether or not a circle uses that edge. -/
theorem exists_light_circle_edge [DecidableRel G.Adj]
    (hsum : (∑ x : V, cycleDegree G x) = 20160)
    (hdeg : ∀ x : V, 361 ≤ cycleDegree G x)
    (hE : ∀ ⦃x y : V⦄, G.Adj x y →
      360 ≤ (TaskH.modCyclesThroughAvoid 7 G x y).ncard)
    (hn : 46 ≤ Fintype.card V) :
    ∃ x y : V, G.Adj x y ∧ cycleDegree G x ≤ 438 ∧
      1 ≤ (jointCircleFinset G x y).card ∧ (jointCircleFinset G x y).card ≤ 78 := by
  classical
  obtain ⟨x, hx⟩ := exists_cycleDegree_le_438 hsum hn
  have hpos : 0 < (throughFinset G x).card := by
    have hd := hdeg x
    change 361 ≤ (throughFinset G x).card at hd
    omega
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
  have hCm := (mem_throughFinset C x).mp hC
  obtain ⟨a, p, hp, hset, _hdiv⟩ := Basics.mem_modCycleEdgeSets_iff.mp hCm.1
  have hxp : x ∈ p.support := by
    apply (cycleContains_edges_toFinset_iff p hp.not_nil x).mp
    simpa only [hset] using hCm.2
  let q := p.rotate x hxp
  have hq : q.IsCycle := (Walk.isCycle_rotate hxp).mpr hp
  have hqset : q.edges.toFinset = C := (Basics.rotate_edges_toFinset p x hxp).trans hset
  let y := q.snd
  have hxy : G.Adj x y := q.adj_snd hq.not_nil
  have hCy : CycleContains C y := by
    rw [← hqset]
    exact (cycleContains_edges_toFinset_iff q hq.not_nil y).mpr (q.getVert_mem_support 1)
  have hJ : C ∈ jointCircleFinset G x y := by
    apply Finset.mem_filter.mpr
    exact ⟨(mem_cycleFinset C).mpr hCm.1, hCm.2, hCy⟩
  have hJpos : 1 ≤ (jointCircleFinset G x y).card := by
    have hpositive := Finset.card_pos.mpr ⟨C, hJ⟩
    omega
  have havoid : 360 ≤ (throughAvoidFinset G x y).card := by
    rw [throughAvoidFinset_card]
    exact hE hxy
  have hpartition := joint_add_throughAvoid (G := G) x y
  exact ⟨x, y, hxy, hx, hJpos, by omega⟩

theorem equality_exists_light_circle_edge [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 7 G) (hc : modCycleCount 7 G = 2880)
    (hn : 46 ≤ Fintype.card V) :
    ∃ x y : V, G.Adj x y ∧ cycleDegree G x ≤ 438 ∧
      1 ≤ (jointCircleFinset G x y).card ∧ (jointCircleFinset G x y).card ≤ 78 :=
  exists_light_circle_edge (equality_sum_cycleDegree hcrit hc)
    (equality_three_hundred_sixty_one_le_cycleDegree hcrit hc)
    (fun {x y : V} hxy =>
      equality_edge_three_hundred_sixty_modCyclesThroughAvoid hcrit hc (x := x) (y := y) hxy) hn

end TaskH.Seven

#print axioms TaskH.Seven.jointCircleFinset
#print axioms TaskH.Seven.nonbadCircleFinset
#print axioms TaskH.Seven.joint_add_nonbad
#print axioms TaskH.Seven.joint_add_throughAvoid
#print axioms TaskH.Seven.exists_cycleDegree_le_438
#print axioms TaskH.Seven.exists_light_circle_edge
#print axioms TaskH.Seven.equality_exists_light_circle_edge
