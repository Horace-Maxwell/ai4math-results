import Research.TaskH.Gao.IdentificationDegree

/-! Original case2's actual rooted four-cycle witness and its zero identification loss.
The remaining actual-component/IH/path transport is separate, not assumed here. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def Case2RootQuad (G : SimpleGraph V) (x y : V) : Prop :=
  x ≠ y ∧ ∃ a b c : V, a ≠ c ∧ x ≠ b ∧ a ≠ y ∧ b ≠ y ∧ c ≠ y ∧
    G.Adj x a ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c x

theorem case2_quad_from_two_common_neighbors (G : SimpleGraph V) (x y v : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) (hvx : v ≠ x) (hvy : v ≠ y)
    (a b : V) (ha : a ∈ G.neighborSet v ∩ G.neighborSet x)
    (hb : b ∈ G.neighborSet v ∩ G.neighborSet x) (hab : a ≠ b) :
    Case2RootQuad G x y := by
  have hay : a ≠ y := by
    intro he
    exact hno (Eq.mp (congrArg (fun z : V => G.Adj x z) he) ha.2)
  have hby : b ≠ y := by
    intro he
    exact hno (Eq.mp (congrArg (fun z : V => G.Adj x z) he) hb.2)
  exact ⟨hxy, a, v, b, hab, hvx.symm, hay, hvy, hby,
    ha.2, ha.1.symm, hb.1, hb.2.symm⟩

theorem case2_common_neighbor_ncard_le_one [Finite V] (G : SimpleGraph V)
    (x y : V) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hquad : ¬Case2RootQuad G x y) (v : V) (hvx : v ≠ x) (hvy : v ≠ y) :
    (G.neighborSet v ∩ G.neighborSet x).ncard ≤ 1 := by
  apply (Set.ncard_le_one (Set.toFinite _)).mpr
  intro a ha b hb
  by_contra hab
  exact hquad (case2_quad_from_two_common_neighbors G x y v hxy hno hvx hvy a b ha hb hab)

theorem identification_degree_no_loss_of_neighbor_cap [Finite V]
    (G : SimpleGraph V) (S : Set V) (v : {a : V // a ∉ S})
    (hcap : (G.neighborSet v.1 ∩ S).ncard ≤ 1) :
    (G.neighborSet v.1).ncard ≤
      ((identificationGraph G S).neighborSet (some v)).ncard := by
  classical
  have hb := identification_degree_balance G S v
  by_cases he : ∃ z ∈ S, G.Adj v.1 z
  · have hbit : collapsedNeighborCount G S v.1 = 1 := by
      unfold collapsedNeighborCount
      exact ite_eq_left he
    rw [hbit] at hb
    omega
  · have hem : G.neighborSet v.1 ∩ S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨ez, hz⟩
      exact he ⟨z, hz, ez⟩
    have hbit : collapsedNeighborCount G S v.1 = 0 := by
      unfold collapsedNeighborCount
      exact ite_eq_right he
    rw [hem, Set.ncard_empty, hbit] at hb
    omega

theorem case2_identification_degree_no_loss [Finite V] (G : SimpleGraph V)
    (x y : V) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hquad : ¬Case2RootQuad G x y) (S : Set V) (hS : S ⊆ G.neighborSet x)
    (v : {a : V // a ∉ S}) (hvx : v.1 ≠ x) (hvy : v.1 ≠ y) :
    (G.neighborSet v.1).ncard ≤
      ((identificationGraph G S).neighborSet (some v)).ncard := by
  have hsub : G.neighborSet v.1 ∩ S ⊆ G.neighborSet v.1 ∩ G.neighborSet x :=
    fun _ hw => ⟨hw.1, hS hw.2⟩
  have hcap := le_trans (Set.ncard_le_ncard hsub)
    (case2_common_neighbor_ncard_le_one G x y hxy hno hquad v.1 hvx hvy)
  exact identification_degree_no_loss_of_neighbor_cap G S v hcap

#print axioms Case2RootQuad
#print axioms case2_quad_from_two_common_neighbors
#print axioms case2_common_neighbor_ncard_le_one
#print axioms identification_degree_no_loss_of_neighbor_cap
#print axioms case2_identification_degree_no_loss
end TaskH.Gao
