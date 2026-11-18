import Research.TaskH.Gao.CaseTwoQuadNeighborDegree
import Research.TaskH.Gao.SingletonG1Quotient
import Research.TaskH.Gao.RootRegionQuotient
import Research.TaskH.Fan.RootNeighborhood

/-! Actual closed-neighborhood components and loss-free original degree transport. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case2_neighbor_card_ge_two [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) : 2 ≤ (G.neighborSet x).ncard := by
  obtain ⟨a, b, hab, exa, exb⟩ := twoConnected_two_root_neighbors G hG x y hxy
  have hs : ({a, b} : Set V) ⊆ G.neighborSet x := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with he | he
    · exact Eq.mpr (congrArg (fun v : V => G.Adj x v) he) exa
    · have he' : z = b := he
      exact Eq.mpr (congrArg (fun v : V => G.Adj x v) he') exb
  have hn := Set.ncard_le_ncard hs
  rw [Set.ncard_pair hab] at hn
  exact hn

theorem case2_closed_card_ge_three [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y) :
    3 ≤ (closedRootNeighborhood G x).ncard := by
  let : Fintype (closedRootNeighborhood G x) := Fintype.ofFinite _
  have hn := closedRootNeighborhood_card G hG x y hxy
  simpa only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq] using hn

theorem case2_component_neighbors_full (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) :
    ∀ a ∈ singletonG1Vertices G K C, ∀ z, G.Adj a z →
      z ∈ singletonG1Vertices G K C ∪ singletonG1Boundary G K C := by
  rintro a ⟨haK, haC⟩ z e
  let ar : C.supp := ⟨⟨a, haK⟩, haC⟩
  rcases singleton_g1_full_neighbor_cover G K C ar z e with hzK | hzR
  · exact Or.inr ⟨hzK, ar, e⟩
  · exact Or.inl hzR

theorem case2_closed_boundary_subset (G : SimpleGraph V) (x : V)
    (C : (G.induce (closedRootNeighborhood G x)ᶜ).ConnectedComponent) :
    singletonG1Boundary G (closedRootNeighborhood G x) C ⊆ G.neighborSet x := by
  rintro a ⟨haK, d, eda⟩
  rcases haK with hax | hax
  · have exd : G.Adj x d.1.1 :=
      Eq.mp (congrArg (fun v : V => G.Adj v d.1.1) hax) eda.symm
    exact False.elim (d.1.2 (Or.inr exd))
  · exact hax

theorem case2_induced_identification_degree [Fintype V] (G : SimpleGraph V)
    (x y : V) (k : ℕ) (hxy : x ≠ y) (hno : ¬G.Adj x y)
    (hquad : ¬Case2RootQuad G x y) (T : Set V) (S : Set T)
    (u : {a : T // a ∉ S})
    (hS : ∀ z ∈ S, z.1 ∈ G.neighborSet x)
    (hpoints : ∀ a : {z : T // z ∉ S}, a ≠ u → a.1.1 ≠ x ∧ a.1.1 ≠ y)
    (hfull : ∀ a : {z : T // z ∉ S}, a ≠ u → ∀ z, G.Adj a.1.1 z → z ∈ T)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (identificationGraph (G.induce T) S) none (some u) (k + 1) := by
  classical
  let J := G.induce T
  intro q hqn hqu
  cases q with
  | none => exact False.elim (hqn rfl)
  | some a =>
    have hau : a ≠ u := fun he => hqu (congrArg Option.some he)
    have hcap : (J.neighborSet a.1 ∩ S).ncard ≤ 1 := by
      calc
        (J.neighborSet a.1 ∩ S).ncard ≤
            (G.neighborSet a.1.1 ∩ G.neighborSet x).ncard :=
          Set.ncard_le_ncard_of_injOn (fun z : T => z.1)
            (fun z hz => ⟨hz.1, hS z hz.2⟩) (fun _ _ _ _ he => Subtype.ext he)
        _ ≤ 1 := case2_common_neighbor_ncard_le_one G x y hxy hno hquad a.1.1
          (hpoints a hau).1 (hpoints a hau).2
    have hf : (J.neighborSet a.1).ncard = (G.neighborSet a.1.1).ncard := by
      apply Set.ncard_congr (fun z _ => z.1)
      · intro z hz; exact hz
      · intro z w _ _ he; exact Subtype.ext he
      · intro z hz; exact ⟨⟨z, hfull a hau z hz⟩, hz, rfl⟩
    have hOrig := hd a.1.1 (hpoints a hau).1 (hpoints a hau).2
    rw [← hf] at hOrig
    exact le_trans hOrig (identification_degree_no_loss_of_neighbor_cap J S a hcap)

theorem case2_closed_component_strict_order [Fintype V] (G : SimpleGraph V) (x y : V)
    (hG : TwoConnected G) (hxy : x ≠ y)
    (C : (G.induce (closedRootNeighborhood G x)ᶜ).ConnectedComponent) :
    (singletonG1Vertices G (closedRootNeighborhood G x) C).ncard + 1 < Nat.card V := by
  let N := singletonG1Vertices G (closedRootNeighborhood G x) C
  have hdis : Disjoint N (closedRootNeighborhood G x) := by
    apply Set.disjoint_left.mpr
    rintro a ⟨haK, _⟩ ha
    exact haK ha
  have hn := Set.ncard_le_card (N ∪ closedRootNeighborhood G x)
  rw [Set.ncard_union_eq hdis] at hn
  change (singletonG1Vertices G (closedRootNeighborhood G x) C).ncard +
    (closedRootNeighborhood G x).ncard ≤ Nat.card V at hn
  have hK := case2_closed_card_ge_three G x y hG hxy
  omega

theorem case2_small_component_neighbors_subset [Fintype V] (G : SimpleGraph V) (x y : V)
    (hno : ¬G.Adj x y)
    (C : (G.induce (closedRootNeighborhood G x)ᶜ).ConnectedComponent)
    (hyC : y ∈ singletonG1Vertices G (closedRootNeighborhood G x) C)
    (hsmall : (singletonG1Vertices G (closedRootNeighborhood G x) C).ncard ≤ 1) :
    G.neighborSet y ⊆ G.neighborSet x := by
  intro z eyz
  have hyK := hyC.1
  let yr : C.supp := ⟨⟨y, hyK⟩, hyC.2⟩
  rcases singleton_g1_full_neighbor_cover G (closedRootNeighborhood G x) C yr z eyz with hzK | hzC
  · rcases hzK with hzx | hxz
    · have eyx : G.Adj y x := Eq.mp (congrArg (fun v : V => G.Adj y v) hzx) eyz
      exact False.elim (hno eyx.symm)
    · exact hxz
  · have hzy : z = y := (Set.ncard_le_one (Set.toFinite _)).mp hsmall z hzC y hyC
    exact False.elim (G.irrefl (Eq.mp (congrArg (fun v : V => G.Adj y v) hzy) eyz))

#print axioms case2_neighbor_card_ge_two
#print axioms case2_closed_card_ge_three
#print axioms case2_component_neighbors_full
#print axioms case2_closed_boundary_subset
#print axioms case2_induced_identification_degree
#print axioms case2_closed_component_strict_order
#print axioms case2_small_component_neighbors_subset
end TaskH.Gao
