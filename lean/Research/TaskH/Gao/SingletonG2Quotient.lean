import Research.TaskH.Gao.IdentificationDegree
import Research.TaskH.Fan.IdentificationConnectivity

/-! The actual G2 is G-y with precisely N_G(y) identified; no free edges. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def singletonG2Collapse (G : SimpleGraph V) (y : V) : Set {z : V // z ≠ y} :=
  {z | G.Adj y z.1}

def singletonG2Graph (G : SimpleGraph V) (y : V) :
    SimpleGraph (IdentificationVertex (singletonG2Collapse G y)) :=
  identificationGraph (G.induce {z : V | z ≠ y}) (singletonG2Collapse G y)

@[instance_reducible]
noncomputable def singletonG2Fintype [Fintype V] (G : SimpleGraph V) (y : V) :
    Fintype (IdentificationVertex (singletonG2Collapse G y)) := Fintype.ofFinite _

def singletonG2Root (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) :
    {z : {v : V // v ≠ y} // z ∉ singletonG2Collapse G y} :=
  ⟨⟨x, hxy⟩, fun e => hno e.symm⟩

theorem singleton_g2_collapse_ncard (G : SimpleGraph V) (y : V) :
    (singletonG2Collapse G y).ncard = (G.neighborSet y).ncard := by
  apply Set.ncard_congr (fun z _ => z.1)
  · intro z hz
    exact hz
  · intro a b _ha _hb he
    exact Subtype.ext he
  · intro z hz
    exact ⟨⟨z, hz.ne.symm⟩, hz, rfl⟩

theorem singleton_g2_order_balance [Fintype V] (G : SimpleGraph V) (y : V) :
    Nat.card (IdentificationVertex (singletonG2Collapse G y)) +
      (G.neighborSet y).ncard = Nat.card V := by
  classical
  let U := {z : V // z ≠ y}
  let S := singletonG2Collapse G y
  let : Fintype U := Fintype.ofFinite _
  let : Fintype {z : V // z = y} := Fintype.ofFinite _
  let : Fintype {z : U // z ∉ S} := Fintype.ofFinite _
  have hu : Nat.card U + 1 = Nat.card V := by
    have hh := Fintype.card_subtype_compl (fun z : V => z = y)
    have hy : Fintype.card {z : V // z = y} = 1 := Fintype.card_subtype_eq y
    rw [hy] at hh
    have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨y⟩
    simp only [Fintype.card_eq_nat_card] at hh hp
    change Nat.card U = Nat.card V - 1 at hh
    omega
  have ho : Nat.card (IdentificationVertex S) =
      Nat.card {z : U // z ∉ S} + 1 := by
    simpa only [IdentificationVertex, Fintype.card_eq_nat_card] using
      (Fintype.card_option (α := {z : U // z ∉ S}))
  have hp : S.ncard + Sᶜ.ncard = Nat.card U := Set.ncard_add_ncard_compl S
  have hs : S.ncard = (G.neighborSet y).ncard := singleton_g2_collapse_ncard G y
  have hc : Nat.card {z : U // z ∉ S} = Sᶜ.ncard := Nat.card_coe_set_eq _
  change Nat.card (IdentificationVertex S) + (G.neighborSet y).ncard = Nat.card V
  omega

theorem singleton_g2_strict_order [Fintype V] (G : SimpleGraph V) (y : V)
    (hm : 1 ≤ (G.neighborSet y).ncard) :
    Nat.card (IdentificationVertex (singletonG2Collapse G y)) < Nat.card V := by
  have h := singleton_g2_order_balance G y
  omega

theorem singleton_g2_original_neighbor_ncard [Finite V] (G : SimpleGraph V)
    (y : V) (z : {v : {a : V // a ≠ y} // v ∉ singletonG2Collapse G y}) :
    ((G.induce {a : V | a ≠ y}).neighborSet z.1).ncard =
      (G.neighborSet z.1.1).ncard := by
  apply Set.ncard_congr (fun a _ => a.1)
  · intro a ha
    exact ha
  · intro a b _ha _hb he
    exact Subtype.ext he
  · intro a ha
    have hay : a ≠ y := by
      intro he
      have ezy : G.Adj z.1.1 y := Eq.mp
        (congrArg (fun v : V => G.Adj z.1.1 v) he) ha
      exact z.2 ezy.symm
    exact ⟨⟨a, hay⟩, ha, rfl⟩

theorem singleton_g2_degree_loss_bound [Finite V] (G : SimpleGraph V) (y : V)
    (hm : 1 ≤ (G.neighborSet y).ncard)
    (z : {v : {a : V // a ≠ y} // v ∉ singletonG2Collapse G y}) :
    (G.neighborSet z.1.1).ncard ≤
      ((singletonG2Graph G y).neighborSet (some z)).ncard +
        ((G.neighborSet y).ncard - 1) := by
  classical
  let J := G.induce {a : V | a ≠ y}
  let S := singletonG2Collapse G y
  have hb := identification_degree_balance J S z
  have hz := singleton_g2_original_neighbor_ncard G y z
  have hs := singleton_g2_collapse_ncard G y
  have hi : (J.neighborSet z.1 ∩ S).ncard ≤ S.ncard :=
    Set.ncard_le_ncard Set.inter_subset_right
  by_cases he : ∃ a ∈ S, J.Adj z.1 a
  · have hc : collapsedNeighborCount J S z.1 = 1 := by
      unfold collapsedNeighborCount
      exact ite_eq_left he
    change ((singletonG2Graph G y).neighborSet (some z)).ncard +
      (J.neighborSet z.1 ∩ S).ncard = (J.neighborSet z.1).ncard +
        collapsedNeighborCount J S z.1 at hb
    rw [hz, hc] at hb
    have hi' : (J.neighborSet z.1 ∩ S).ncard ≤ (G.neighborSet y).ncard :=
      le_trans hi (le_of_eq hs)
    omega
  · have hc : collapsedNeighborCount J S z.1 = 0 := by
      unfold collapsedNeighborCount
      exact ite_eq_right he
    have hem : J.neighborSet z.1 ∩ S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro a ⟨ha, haS⟩
      exact he ⟨a, haS, ha⟩
    rw [hem, Set.ncard_empty, hc, add_zero, add_zero] at hb
    change ((singletonG2Graph G y).neighborSet (some z)).ncard =
      (J.neighborSet z.1).ncard at hb
    rw [hz] at hb
    omega

theorem singleton_g2_nonroot_degree [Finite V] (G : SimpleGraph V)
    (x y : V) (hxy : x ≠ y) (hno : ¬G.Adj x y) (k : ℕ)
    (hm : 1 ≤ (G.neighborSet y).ncard) (hmk : (G.neighborSet y).ncard ≤ k)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (singletonG2Graph G y)
      (some (singletonG2Root G x y hxy hno)) none
      (k - (G.neighborSet y).ncard + 2) := by
  intro z hzx hzn
  cases z with
  | none => exact False.elim (hzn rfl)
  | some z =>
    have hzx' : z.1.1 ≠ x := by
      intro he
      apply hzx
      exact congrArg Option.some (Subtype.ext (Subtype.ext he))
    have hb := singleton_g2_degree_loss_bound G y hm z
    have hz := hd z.1.1 hzx' z.1.2
    omega

#print axioms singletonG2Collapse
#print axioms singletonG2Graph
#print axioms singletonG2Fintype
#print axioms singletonG2Root
#print axioms singleton_g2_collapse_ncard
#print axioms singleton_g2_order_balance
#print axioms singleton_g2_strict_order
#print axioms singleton_g2_original_neighbor_ncard
#print axioms singleton_g2_degree_loss_bound
#print axioms singleton_g2_nonroot_degree
end TaskH.Gao
