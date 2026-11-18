import Research.TaskH.Gao.CaseTwoActualComponents
import Research.TaskH.Gao.IdentificationFamilyLift

/-! A genuine nonsingleton y-component gives original k paths, with one real prefix edge. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case2_large_y_original_family [Fintype V] (G : SimpleGraph V) (x y : V) (k : ℕ)
    (hG : TwoConnected G) (hxy : x ≠ y) (hno : ¬G.Adj x y) (hk : 1 ≤ k)
    (hquad : ¬Case2RootQuad G x y)
    (C : (G.induce (closedRootNeighborhood G x)ᶜ).ConnectedComponent)
    (hyC : y ∈ singletonG1Vertices G (closedRootNeighborhood G x) C)
    (hlarge : 2 ≤ (singletonG1Vertices G (closedRootNeighborhood G x) C).ncard)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths G x y k := by
  classical
  let K := closedRootNeighborhood G x
  let N := singletonG1Vertices G K C
  let S := singletonG1Boundary G K C
  have hsub : S ⊆ G.neighborSet x := case2_closed_boundary_subset G x C
  have hdis : Disjoint N S := by
    apply Set.disjoint_left.mpr
    rintro a ⟨haK, _⟩ haS
    exact haK haS.1
  have hK := case2_closed_card_ge_three G x y hG hxy
  change 3 ≤ K.ncard at hK
  have hS : S.Nonempty := by
    obtain ⟨a, ha, _b, _hb, _hab⟩ := singleton_g1_two_boundary_points G K C x hG (Or.inl rfl) (by omega)
    exact ⟨a, ha⟩
  let T := N ∪ S
  let SC : Set T := {z | z.1 ∈ S}
  let yr : {z : T // z ∉ SC} := regionRetainedVertex N S hdis ⟨y, hyC⟩
  let : Fintype (IdentificationVertex SC) := Fintype.ofFinite _
  have hclose := case2_component_neighbors_full G K C
  have hr : RootedTwoConnected (regionIdentificationGraph G N S) none (some yr) :=
    rootRegion_quotient_rooted G N S hdis ⟨y, hyC⟩ hS
      (singleton_g1_interior_connected G K C) hlarge
      (fun a ha _hne z e => hclose a ha z e) hG
  have hp : ∀ a : {z : T // z ∉ SC}, a ≠ yr → a.1.1 ≠ x ∧ a.1.1 ≠ y := by
    intro a hay
    have haN : a.1.1 ∈ N := a.1.2.elim id (fun haS => False.elim (a.2 haS))
    have hax : a.1.1 ≠ x := fun he => haN.1
      (Eq.mpr (congrArg (fun v : V => v ∈ K) he) (Or.inl rfl))
    have hay' : a.1.1 ≠ y := fun he => hay (Subtype.ext (Subtype.ext he))
    exact ⟨hax, hay'⟩
  have hf : ∀ a : {z : T // z ∉ SC}, a ≠ yr → ∀ z, G.Adj a.1.1 z → z ∈ T := by
    intro a _ha z e
    have haN : a.1.1 ∈ N := a.1.2.elim id (fun haS => False.elim (a.2 haS))
    exact hclose a.1.1 haN z e
  have hdegree := case2_induced_identification_degree G x y k hxy hno hquad T SC yr
    (fun z hz => hsub hz) hp hf hd
  have horder : Nat.card (IdentificationVertex SC) < Nat.card V := by
    have hn := case2_closed_component_strict_order G x y hG hxy C
    change Nat.card (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S}) < Nat.card V
    rw [regionIdentification_card N S hdis]
    exact hn
  have horder' : Fintype.card (IdentificationVertex SC) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using horder
  have hchild := ih (IdentificationVertex SC) (regionIdentificationGraph G N S) none (some yr)
    k horder' hk hr hdegree
  obtain ⟨a, step, paths, hpaths⟩ := hchild
  obtain ⟨v, q, hv, hfam, _hlen, hsupp⟩ := identification_induced_family_lift G T S yr k a step paths hpaths
  dsimp only [yr, regionRetainedVertex] at q hfam
  have hxT : x ∉ T := by
    rintro (hxN | hxS)
    · exact hxN.1 (Or.inl rfl)
    · exact G.irrefl (hsub hxS)
  have hxq : ∀ i, x ∉ (q i).support := fun i hz => hxT (hsupp i x hz).1
  let ps : Fin k → G.Walk x y := fun i => Walk.cons (hsub (hv i)) (q i)
  refine ⟨a + 1, step, ps, by have hh := hfam.1; omega, hfam.2.1, ?_⟩
  intro i
  refine ⟨(hfam.2.2 i).1.cons (hxq i), ?_⟩
  change (q i).length + 1 = a + 1 + i.val * step
  rw [(hfam.2.2 i).2]
  omega

#print axioms case2_large_y_original_family
end TaskH.Gao
