import Research.Backfill.Paper7.SunCycleSupport
import Research.Backfill.Paper7.SunPQCardinality

/-! The actual edge set is partitioned into cycle edges and one inward edge
for every arm vertex. This includes zero-length arms and arbitrary arm lists. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph BackfillPaper7.Challenge
open scoped Classical

namespace Paper7SunMoments

abbrev SunArm (b : ℕ) (L : Fin b → List ℕ) :=
  Σ k : Fin b, Σ j : Fin (L k).length, Fin ((L k).get j)

def sunParent {b : ℕ} {L : Fin b → List ℕ} (z : SunArm b L) : SunV b L :=
  if h : z.2.2.val = 0 then Sum.inl z.1
  else Sum.inr ⟨z.1, z.2.1, ⟨z.2.2.val - 1, by have := z.2.2.isLt; omega⟩⟩

theorem sun_parent_adj {b : ℕ} {L : Fin b → List ℕ} (z : SunArm b L) :
    (sunGraph b L).Adj (Sum.inr z) (sunParent z) := by
  rcases z with ⟨k, j, a⟩
  unfold sunParent
  split_ifs with h <;> dsimp only at *
  · exact (Paper7Cleared.sun_arm_root_adj_iff b L k k j a).mpr ⟨rfl, h⟩
  · apply (Paper7Cleared.sun_arm_adj_iff b L k k j j a _).mpr
    refine ⟨rfl, rfl, Or.inr ?_⟩
    change a.val - 1 + 1 = a.val
    omega

theorem sun_parent_depth_lt {b : ℕ} {L : Fin b → List ℕ} (z : SunArm b L) :
    sunDepth (sunParent z) < sunDepth (Sum.inr z) := by
  rcases z with ⟨k, j, a⟩
  unfold sunParent
  split_ifs with h <;> dsimp only [sunDepth] at * <;> omega

def sunParentEdge {b : ℕ} {L : Fin b → List ℕ} (z : SunArm b L) : Sym2 (SunV b L) :=
  s(Sum.inr z, sunParent z)

theorem sunParentEdge_injective {b : ℕ} {L : Fin b → List ℕ} :
    Function.Injective (@sunParentEdge b L) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Sum.inr.inj h.1
  · have hx := sun_parent_depth_lt x
    have hy := sun_parent_depth_lt y
    have h1 := congrArg sunDepth h.1
    have h2 := congrArg sunDepth h.2
    omega

def sunRootEdges (b : ℕ) (L : Fin b → List ℕ) : Finset (Sym2 (SunV b L)) :=
  (SimpleGraph.cycleGraph b).edgeFinset.image (Sym2.map Sum.inl)

def sunArmEdges (b : ℕ) (L : Fin b → List ℕ) : Finset (Sym2 (SunV b L)) :=
  Finset.univ.image sunParentEdge

theorem sunRootEdges_disjoint_armEdges (b : ℕ) (L : Fin b → List ℕ) :
    Disjoint (sunRootEdges b L) (sunArmEdges b L) := by
  apply Finset.disjoint_left.mpr
  intro e he ha
  obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨z, _hz, hz⟩ := Finset.mem_image.mp ha
  induction q using Sym2.inductionOn with
  | hf i j => simp [sunParentEdge] at hz

theorem sun_edgeFinset_partition (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) :
    (sunGraph b L).edgeFinset = sunRootEdges b L ∪ sunArmEdges b L := by
  ext e
  constructor
  · intro he
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hxy : (sunGraph b L).Adj x y :=
        SimpleGraph.mem_edgeFinset.mp he
      cases x with
      | inl i =>
        cases y with
        | inl j =>
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨s(i, j), ?_, rfl⟩
          exact SimpleGraph.mem_edgeFinset.mpr
            ((Paper7Cleared.sun_cycle_adj_iff b L hb i j).mp hxy)
        | inr z =>
          have hp : Sum.inl i = sunParent z := sun_lower_neighbor_unique hxy.symm
            (sun_parent_adj z) (by simp only [sunDepth]; omega) (sun_parent_depth_lt z)
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨z, Finset.mem_univ _, Sym2.eq_iff.mpr (Or.inr ⟨rfl, hp.symm⟩)⟩
      | inr x =>
        cases y with
        | inl i =>
          have hp : Sum.inl i = sunParent x := sun_lower_neighbor_unique hxy
            (sun_parent_adj x) (by simp only [sunDepth]; omega) (sun_parent_depth_lt x)
          apply Finset.mem_union_right
          apply Finset.mem_image.mpr
          refine ⟨x, Finset.mem_univ _, Sym2.eq_iff.mpr (Or.inl ⟨rfl, hp.symm⟩)⟩
        | inr y =>
          have hne := sun_adj_depth_ne_of_pos (by simp only [sunDepth]; omega) hxy
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hp : Sum.inr x = sunParent y := sun_lower_neighbor_unique hxy.symm
              (sun_parent_adj y) hlt (sun_parent_depth_lt y)
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            exact ⟨y, Finset.mem_univ _, Sym2.eq_iff.mpr (Or.inr ⟨rfl, hp.symm⟩)⟩
          · have hp : Sum.inr y = sunParent x := sun_lower_neighbor_unique hxy
              (sun_parent_adj x) hgt (sun_parent_depth_lt x)
            apply Finset.mem_union_right
            apply Finset.mem_image.mpr
            exact ⟨x, Finset.mem_univ _, Sym2.eq_iff.mpr (Or.inl ⟨rfl, hp.symm⟩)⟩
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
      induction q using Sym2.inductionOn with
      | hf i j =>
        apply SimpleGraph.mem_edgeFinset.mpr
        change (sunGraph b L).Adj (Sum.inl i) (Sum.inl j)
        exact (Paper7Cleared.sun_cycle_adj_iff b L hb i j).mpr
          (SimpleGraph.mem_edgeFinset.mp hq)
    · obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp he
      exact SimpleGraph.mem_edgeFinset.mpr (sun_parent_adj z)

theorem cycleGraph_edge_card (b : ℕ) (hb : 3 ≤ b) :
    (SimpleGraph.cycleGraph b).edgeFinset.card = b := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 3 := ⟨b - 3, by omega⟩
  have h := (SimpleGraph.cycleGraph (n + 3)).sum_degrees_eq_twice_card_edges
  simp only [SimpleGraph.cycleGraph_degree_three_le, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

theorem sun_edge_card_eq_vertex_card (b : ℕ) (L : Fin b → List ℕ) (hb : 3 ≤ b) :
    (sunGraph b L).edgeFinset.card = Fintype.card (SunV b L) := by
  rw [sun_edgeFinset_partition b L hb,
    Finset.card_union_of_disjoint (sunRootEdges_disjoint_armEdges b L)]
  have hroot : (sunRootEdges b L).card = b := by
    rw [sunRootEdges, Finset.card_image_of_injective _ (Sym2.map.injective Sum.inl_injective)]
    exact cycleGraph_edge_card b hb
  have harm : (sunArmEdges b L).card = Fintype.card (SunArm b L) := by
    rw [sunArmEdges, Finset.card_image_of_injective _ sunParentEdge_injective, Finset.card_univ]
  rw [hroot, harm]
  simp only [SunV, Fintype.card_sum, Fintype.card_fin]

theorem sg_edge_card (b : ℕ) (p q : Fin b → ℕ) (hb : 3 ≤ b) :
    (SG b p q).edgeFinset.card = nOf b p q := by
  rw [sun_edge_card_eq_vertex_card b (pq b p q) hb, Paper7Cleared.card_sun_pq]
  rfl

end Paper7SunMoments

#print axioms Paper7SunMoments.SunArm
#print axioms Paper7SunMoments.sunParent
#print axioms Paper7SunMoments.sun_parent_adj
#print axioms Paper7SunMoments.sun_parent_depth_lt
#print axioms Paper7SunMoments.sunParentEdge
#print axioms Paper7SunMoments.sunParentEdge_injective
#print axioms Paper7SunMoments.sunRootEdges
#print axioms Paper7SunMoments.sunArmEdges
#print axioms Paper7SunMoments.sunRootEdges_disjoint_armEdges
#print axioms Paper7SunMoments.sun_edgeFinset_partition
#print axioms Paper7SunMoments.cycleGraph_edge_card
#print axioms Paper7SunMoments.sun_edge_card_eq_vertex_card
#print axioms Paper7SunMoments.sg_edge_card
