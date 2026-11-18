import Research.TaskH.Gao.SingletonG1Quotient

/-! Primary580–585: actual G-(A union B union {y}) component and its full B-x boundary. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def bicliqueSingletonCore (A B : Set V) (y : V) : Set V := (A ∪ B) ∪ {y}

theorem biclique_first_core_card [Fintype V] (A B : Set V) (y : V) (s : ℕ)
    (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hB : B.ncard = s + 1) :
    3 ≤ (bicliqueSingletonCore A B y).ncard := by
  have hyB : y ∉ B := fun h => hy (Or.inr h)
  have hsub : B ∪ {y} ⊆ bicliqueSingletonCore A B y := by
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  have hc := Set.ncard_le_ncard hsub
  rw [Set.union_singleton, Set.ncard_insert_of_notMem hyB, hB] at hc
  omega

theorem biclique_first_boundary_subset [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ¬∃ a ∈ A, ∃ d : C.supp, G.Adj a d.1.1) :
    singletonG1Boundary G (bicliqueSingletonCore A B y) C ⊆ B \ {x} := by
  rintro a ⟨haK, d, eda⟩
  have haA : a ∉ A := fun ha => hnoA ⟨a, ha, d, eda.symm⟩
  have hay : a ≠ y := by
    intro he
    have edy : G.Adj y d.1.1 := Eq.mp
      (congrArg (fun z : V => G.Adj z d.1.1) he) eda.symm
    have hdA : d.1.1 ∈ A :=
      Eq.mp (congrArg (fun S : Set V => d.1.1 ∈ S) hNy) edy
    exact d.1.2 (Or.inl (Or.inl hdA))
  have hax : a ≠ x := by
    intro he
    have edx : G.Adj x d.1.1 := Eq.mp
      (congrArg (fun z : V => G.Adj z d.1.1) he) eda.symm
    have hdA : d.1.1 ∈ A :=
      Eq.mp (congrArg (fun S : Set V => d.1.1 ∈ S) hNx) edx
    exact d.1.2 (Or.inl (Or.inl hdA))
  refine ⟨?_, hax⟩
  rcases haK with (ha | ha) | ha
  · exact False.elim (haA ha)
  · exact ha
  · exact False.elim (hay ha)

theorem biclique_first_two_boundary_forces_s [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hx : x ∈ B) (hy : y ∉ A ∪ B)
    (hs : 1 ≤ s) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ¬∃ a ∈ A, ∃ d : C.supp, G.Adj a d.1.1) :
    2 ≤ s ∧ 2 ≤ (singletonG1Boundary G (bicliqueSingletonCore A B y) C).ncard ∧
      (singletonG1Boundary G (bicliqueSingletonCore A B y) C).ncard ≤ s := by
  have hK := biclique_first_core_card A B y s hy hs hB
  have htwo := singleton_g1_boundary_ncard_ge_two G (bicliqueSingletonCore A B y) C x
    hG (Or.inl (Or.inr hx)) (by omega)
  have hle := Set.ncard_le_ncard (biclique_first_boundary_subset G A B x y C hNx hNy hnoA)
  rw [Set.ncard_sdiff_singleton_of_mem hx, hB] at hle
  exact ⟨by omega, htwo, by omega⟩

theorem biclique_first_collapse_ncard (G : SimpleGraph V) (K : Set V)
    (C : (G.induce Kᶜ).ConnectedComponent) (u : V) :
    (boundaryCollapse G (singletonG1Vertices G K C) u).ncard =
      (singletonG1Boundary G K C \ {u}).ncard := by
  apply Set.ncard_congr (fun z _ => z.1)
  · intro z hz
    have hh := hz.1
    rw [singleton_g1_full_boundary G K C] at hh
    exact ⟨hh, hz.2⟩
  · intro a b _ha _hb he
    exact Subtype.ext he
  · intro z hz
    have hb : z ∈ equalBranchBoundary G (singletonG1Vertices G K C) := by
      rw [singleton_g1_full_boundary G K C]
      exact hz.1
    exact ⟨⟨z, Or.inr hb⟩, ⟨hb, hz.2⟩, rfl⟩

theorem biclique_first_strict_order [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (y u : V) (s : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hB : B.ncard = s + 1)
    (hu : u ∈ singletonG1Boundary G (bicliqueSingletonCore A B y) C) :
    Nat.card (IdentificationVertex
      (boundaryCollapse G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u)) < Nat.card V := by
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  have hdis : Disjoint R K := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hz, _hzC⟩ hzK
    exact hz hzK
  have hn := Set.ncard_le_card (R ∪ K)
  rw [Set.ncard_union_eq hdis] at hn
  have hK := biclique_first_core_card A B y s hy hs hB
  change 3 ≤ K.ncard at hK
  have hR : R.ncard = Nat.card C.supp := singletonG1Vertices_ncard G K C
  rw [singleton_g1_order G K C u hu]
  omega

#print axioms bicliqueSingletonCore
#print axioms biclique_first_core_card
#print axioms biclique_first_boundary_subset
#print axioms biclique_first_two_boundary_forces_s
#print axioms biclique_first_collapse_ncard
#print axioms biclique_first_strict_order
end TaskH.Gao
