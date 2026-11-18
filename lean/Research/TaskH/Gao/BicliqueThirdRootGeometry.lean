import Research.TaskH.Gao.RootRegionQuotient
import Research.TaskH.Gao.BicliqueSingletonFirstGeometry
import Research.TaskH.Gao.OneRootExtension

/-! Actual component geometry for BOTH alternatives in primary606–610. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def bicliqueThirdCollapse (G : SimpleGraph V) (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) : Set V :=
  {b | b ∈ B \ {x} ∧ ∃ d : C.supp, G.Adj d.1.1 b}

def bicliqueThirdRetained (G : SimpleGraph V) (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) : Set V :=
  singletonG1Vertices G (bicliqueSingletonCore A B y) C ∪ {u}

def BicliqueThirdRootCase (G : SimpleGraph V) (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) : Prop :=
  (u ∈ A ∧ (∃ d : C.supp, G.Adj d.1.1 u) ∧
    ∀ (d : C.supp) a, a ∈ A → G.Adj d.1.1 a → a = u) ∨
  (u ∈ singletonG1Vertices G (bicliqueSingletonCore A B y) C ∧
    ∀ (d : C.supp) a, a ∈ A → G.Adj d.1.1 a → d.1.1 = u)

theorem biclique_third_component_neighbor_cover (G : SimpleGraph V)
    (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (d : C.supp) (z : V) (e : G.Adj d.1.1 z) :
    z ∈ singletonG1Vertices G (bicliqueSingletonCore A B y) C ∨
      z ∈ A ∨ z ∈ B \ {x} := by
  have hzx : z ≠ x := by
    intro he
    have ex : G.Adj x d.1.1 := Eq.mp
      (congrArg (fun v : V => G.Adj v d.1.1) he) e.symm
    have hdA : d.1.1 ∈ A :=
      Eq.mp (congrArg (fun S : Set V => d.1.1 ∈ S) hNx) ex
    exact d.1.2 (Or.inl (Or.inl hdA))
  have hzy : z ≠ y := by
    intro he
    have ey : G.Adj y d.1.1 := Eq.mp
      (congrArg (fun v : V => G.Adj v d.1.1) he) e.symm
    have hdA : d.1.1 ∈ A :=
      Eq.mp (congrArg (fun S : Set V => d.1.1 ∈ S) hNy) ey
    exact d.1.2 (Or.inl (Or.inl hdA))
  rcases singleton_g1_full_neighbor_cover G (bicliqueSingletonCore A B y) C d z e with hzK | hzC
  · rcases hzK with (hzA | hzB) | hzY
    · exact Or.inr (Or.inl hzA)
    · exact Or.inr (Or.inr ⟨hzB, hzx⟩)
    · exact False.elim (hzy hzY)
  · exact Or.inl hzC

theorem biclique_third_component_card_ge_two [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hx : x ∈ B) (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    2 ≤ (singletonG1Vertices G (bicliqueSingletonCore A B y) C).ncard := by
  obtain ⟨d, hdC⟩ := C.nonempty_supp
  let dr : C.supp := ⟨d, hdC⟩
  have hdx : d.1 ≠ x := fun he => d.2
    (Eq.mpr (congrArg (fun v : V => v ∈ bicliqueSingletonCore A B y) he) (Or.inl (Or.inr hx)))
  have hdy : d.1 ≠ y := fun he => d.2
    (Eq.mpr (congrArg (fun v : V => v ∈ bicliqueSingletonCore A B y) he) (Or.inr rfl))
  have hdeg := hd d.1 hdx hdy
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet d.1) (A ∪ B)
  have hsmall := hcap dr
  change (G.neighborSet d.1 ∩ (A ∪ B)).ncard ≤ s + 1 at hsmall
  have hsub : G.neighborSet d.1 \ (A ∪ B) ⊆
      singletonG1Vertices G (bicliqueSingletonCore A B y) C := by
    rintro z ⟨ez, hz⟩
    rcases biclique_third_component_neighbor_cover G A B x y C hNx hNy dr z ez with
      hzR | hzA | hzB
    · exact hzR
    · exact False.elim (hz (Or.inl hzA))
    · exact False.elim (hz (Or.inr hzB.1))
  have hn := Set.ncard_le_ncard hsub
  omega

theorem biclique_third_collapse_card [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hx : x ∈ B) (hB : B.ncard = s + 1) :
    (bicliqueThirdCollapse G A B x y C).ncard ≤ s := by
  have hh : bicliqueThirdCollapse G A B x y C ⊆ B \ {x} := fun _ h => h.1
  have hn := Set.ncard_le_ncard hh
  rw [Set.ncard_sdiff_singleton_of_mem hx, hB] at hn
  omega

theorem biclique_third_disjoint (G : SimpleGraph V) (A B : Set V) (x y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hAB : Disjoint A B) (hcase : BicliqueThirdRootCase G A B y u C) :
    Disjoint (bicliqueThirdRetained G A B y u C) (bicliqueThirdCollapse G A B x y C) := by
  apply Set.disjoint_left.mpr
  rintro z (hzR | hzU) hzS
  · exact hzR.1 (Or.inl (Or.inr hzS.1.1))
  · have he : z = u := hzU
    have huB : u ∈ B := Eq.mp (congrArg (fun v : V => v ∈ B) he) hzS.1.1
    rcases hcase with ⟨huA, _⟩ | ⟨huR, _⟩
    · exact Set.disjoint_left.mp hAB huA huB
    · exact huR.1 (Or.inl (Or.inr huB))

theorem biclique_third_retained_connected (G : SimpleGraph V)
    (A B : Set V) (y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hcase : BicliqueThirdRootCase G A B y u C) :
    (G.induce (bicliqueThirdRetained G A B y u C)).Connected := by
  let R := singletonG1Vertices G (bicliqueSingletonCore A B y) C
  let N := bicliqueThirdRetained G A B y u C
  have hR := singleton_g1_interior_connected G (bicliqueSingletonCore A B y) C
  rcases hcase with ⟨_huA, ⟨d, edu⟩, _hunique⟩ | ⟨huR, _hunique⟩
  · let f : R → N := fun a => ⟨a.1, Or.inl a.2⟩
    have hcover : ∀ p : N, p = ⟨u, Or.inr rfl⟩ ∨ ∃ a : R, f a = p := by
      rintro ⟨z, hzR | hzU⟩
      · exact Or.inr ⟨⟨z, hzR⟩, Subtype.ext rfl⟩
      · exact Or.inl (Subtype.ext hzU)
    exact connected_of_one_extra_vertex (G.induce R) (G.induce N) ⟨u, Or.inr rfl⟩ f
      hR (fun _ _ e => e) hcover ⟨d.1.1, d.1.2, d.2⟩ edu.symm
  · have he : N = R := by
      ext z
      constructor
      · rintro (hz | hz)
        · exact hz
        · exact Eq.mpr (congrArg (fun v : V => v ∈ R) hz) huR
      · exact Or.inl
    change (G.induce N).Connected
    rw [he]
    exact hR

theorem biclique_third_nonroot_full_cover (G : SimpleGraph V)
    (A B : Set V) (x y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcase : BicliqueThirdRootCase G A B y u C) :
    ∀ a ∈ bicliqueThirdRetained G A B y u C, a ≠ u → ∀ b, G.Adj a b →
      b ∈ bicliqueThirdRetained G A B y u C ∪ bicliqueThirdCollapse G A B x y C := by
  intro a ha hau b e
  have haR : a ∈ singletonG1Vertices G (bicliqueSingletonCore A B y) C := by
    rcases ha with ha | ha
    · exact ha
    · exact False.elim (hau ha)
  obtain ⟨haK, haC⟩ := haR
  let ar : C.supp := ⟨⟨a, haK⟩, haC⟩
  rcases biclique_third_component_neighbor_cover G A B x y C hNx hNy ar b e with
    hbR | hbA | hbB
  · exact Or.inl (Or.inl hbR)
  · rcases hcase with ⟨_huA, _witness, hunique⟩ | ⟨_huR, hunique⟩
    · exact Or.inl (Or.inr (hunique ar b hbA e))
    · exact False.elim (hau (hunique ar b hbA e))
  · exact Or.inr ⟨hbB, ar, e⟩

#print axioms bicliqueThirdCollapse
#print axioms bicliqueThirdRetained
#print axioms BicliqueThirdRootCase
#print axioms biclique_third_component_neighbor_cover
#print axioms biclique_third_component_card_ge_two
#print axioms biclique_third_collapse_card
#print axioms biclique_third_disjoint
#print axioms biclique_third_retained_connected
#print axioms biclique_third_nonroot_full_cover
end TaskH.Gao
