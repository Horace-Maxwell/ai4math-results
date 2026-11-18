import Research.TaskH.Gao.BicliqueThirdRootGeometry
import Research.TaskH.Gao.IdentificationDegree
import Research.TaskH.Gao.Challenge

/-! Actual internal-or-external root, strict order, original degree and strict IH. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

@[instance_reducible]
noncomputable def bicliqueThirdFintype [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent) :
    Fintype (IdentificationVertex {z : (bicliqueThirdRetained G A B y u C ∪
      bicliqueThirdCollapse G A B x y C : Set V) | z.1 ∈ bicliqueThirdCollapse G A B x y C}) :=
  Fintype.ofFinite _

theorem biclique_third_quotient_rooted [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B) (hx : x ∈ B)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hcase : BicliqueThirdRootCase G A B y u C)
    (hBtouch : (bicliqueThirdCollapse G A B x y C).Nonempty) :
    @RootedTwoConnected (IdentificationVertex {z : (bicliqueThirdRetained G A B y u C ∪
      bicliqueThirdCollapse G A B x y C : Set V) | z.1 ∈ bicliqueThirdCollapse G A B x y C})
      (bicliqueThirdFintype G A B x y u C)
      (regionIdentificationGraph G (bicliqueThirdRetained G A B y u C)
        (bicliqueThirdCollapse G A B x y C)) none
      (some (regionRetainedVertex (bicliqueThirdRetained G A B y u C)
        (bicliqueThirdCollapse G A B x y C) (biclique_third_disjoint G A B x y u C hAB hcase)
        ⟨u, Or.inr rfl⟩)) := by
  classical
  let N := bicliqueThirdRetained G A B y u C
  let S := bicliqueThirdCollapse G A B x y C
  let : Fintype (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S}) :=
    bicliqueThirdFintype G A B x y u C
  have hR := biclique_third_component_card_ge_two G A B x y s k C hx hs hsk hNx hNy hcap hd
  have hn : (singletonG1Vertices G (bicliqueSingletonCore A B y) C).ncard ≤ N.ncard :=
    Set.ncard_le_ncard (fun _ h => Or.inl h)
  exact rootRegion_quotient_rooted G N S (biclique_third_disjoint G A B x y u C hAB hcase)
    ⟨u, Or.inr rfl⟩ hBtouch (biclique_third_retained_connected G A B y u C hcase)
    (by omega) (biclique_third_nonroot_full_cover G A B x y u C hNx hNy hcase) hG

theorem biclique_third_strict_order [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V) (s : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hAB : Disjoint A B) (hy : y ∉ A ∪ B) (hs : 1 ≤ s) (hB : B.ncard = s + 1)
    (hcase : BicliqueThirdRootCase G A B y u C) :
    Nat.card (IdentificationVertex {z : (bicliqueThirdRetained G A B y u C ∪
      bicliqueThirdCollapse G A B x y C : Set V) | z.1 ∈ bicliqueThirdCollapse G A B x y C}) <
      Nat.card V := by
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  let N := bicliqueThirdRetained G A B y u C
  let S := bicliqueThirdCollapse G A B x y C
  have hdis : Disjoint R K := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hz, _⟩ hzK
    exact hz hzK
  have htotal := Set.ncard_le_card (R ∪ K)
  rw [Set.ncard_union_eq hdis] at htotal
  have hK := biclique_first_core_card A B y s hy hs hB
  change 3 ≤ K.ncard at hK
  have hN : N.ncard ≤ R.ncard + 1 := by
    change (R ∪ {u}).ncard ≤ R.ncard + 1
    rw [Set.union_singleton]
    exact Set.ncard_insert_le u R
  rw [regionIdentification_card N S (biclique_third_disjoint G A B x y u C hAB hcase)]
  omega

theorem biclique_third_order_internal [Finite V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hAB : Disjoint A B) (hcase : BicliqueThirdRootCase G A B y u C)
    (hu : u ∈ singletonG1Vertices G (bicliqueSingletonCore A B y) C) :
    Nat.card (IdentificationVertex {z : (bicliqueThirdRetained G A B y u C ∪
      bicliqueThirdCollapse G A B x y C : Set V) | z.1 ∈ bicliqueThirdCollapse G A B x y C}) =
      Nat.card C.supp + 1 := by
  rw [regionIdentification_card _ _ (biclique_third_disjoint G A B x y u C hAB hcase)]
  change (singletonG1Vertices G (bicliqueSingletonCore A B y) C ∪ {u}).ncard + 1 = _
  rw [Set.union_singleton, Set.ncard_insert_of_mem hu, singletonG1Vertices_ncard]

theorem biclique_third_order_external [Finite V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hAB : Disjoint A B) (hcase : BicliqueThirdRootCase G A B y u C) (hu : u ∈ A) :
    Nat.card (IdentificationVertex {z : (bicliqueThirdRetained G A B y u C ∪
      bicliqueThirdCollapse G A B x y C : Set V) | z.1 ∈ bicliqueThirdCollapse G A B x y C}) =
      Nat.card C.supp + 2 := by
  have huR : u ∉ singletonG1Vertices G (bicliqueSingletonCore A B y) C := by
    intro hh
    exact hh.1 (Or.inl (Or.inl hu))
  rw [regionIdentification_card _ _ (biclique_third_disjoint G A B x y u C hAB hcase)]
  change (singletonG1Vertices G (bicliqueSingletonCore A B y) C ∪ {u}).ncard + 1 = _
  rw [Set.union_singleton, Set.ncard_insert_of_notMem huR, singletonG1Vertices_ncard]

theorem biclique_third_nonroot_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hx : x ∈ B) (hs : 1 ≤ s) (hB : B.ncard = s + 1) (hsk : s ≤ k)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hAB : Disjoint A B) (hcase : BicliqueThirdRootCase G A B y u C)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast
      (regionIdentificationGraph G (bicliqueThirdRetained G A B y u C)
        (bicliqueThirdCollapse G A B x y C)) none
      (some (regionRetainedVertex (bicliqueThirdRetained G A B y u C)
        (bicliqueThirdCollapse G A B x y C) (biclique_third_disjoint G A B x y u C hAB hcase)
        ⟨u, Or.inr rfl⟩)) (k - s + 2) := by
  classical
  let N := bicliqueThirdRetained G A B y u C
  let S := bicliqueThirdCollapse G A B x y C
  let T := N ∪ S
  let J := G.induce T
  let SC : Set T := {z | z.1 ∈ S}
  have hclose := biclique_third_nonroot_full_cover G A B x y u C hNx hNy hcase
  have hSc : SC.ncard = S.ncard := by
    apply Set.ncard_congr (fun z _ => z.1)
    · intro z hz; exact hz
    · intro a b _ _ he; exact Subtype.ext he
    · intro z hz; exact ⟨⟨z, Or.inr hz⟩, hz, rfl⟩
  have hS := biclique_third_collapse_card G A B x y s C hx hB
  change S.ncard ≤ s at hS
  intro q hqn hqu
  cases q with
  | none => exact False.elim (hqn rfl)
  | some a =>
    have hau : a.1.1 ≠ u := by
      intro he
      exact hqu (congrArg Option.some (Subtype.ext (Subtype.ext he)))
    have haN : a.1.1 ∈ N := a.1.2.elim id (fun hs => False.elim (a.2 hs))
    have haR : a.1.1 ∈ singletonG1Vertices G (bicliqueSingletonCore A B y) C := by
      rcases haN with ha | ha
      · exact ha
      · exact False.elim (hau ha)
    have hax : a.1.1 ≠ x := fun he => haR.1
      (Eq.mpr (congrArg (fun v : V => v ∈ bicliqueSingletonCore A B y) he) (Or.inl (Or.inr hx)))
    have hay : a.1.1 ≠ y := fun he => haR.1
      (Eq.mpr (congrArg (fun v : V => v ∈ bicliqueSingletonCore A B y) he) (Or.inr rfl))
    have hOrig := hd a.1.1 hax hay
    have hf : (J.neighborSet a.1).ncard = (G.neighborSet a.1.1).ncard := by
      apply Set.ncard_congr (fun b _ => b.1)
      · intro b hb; exact hb
      · intro b c _ _ he; exact Subtype.ext he
      · intro z hz; exact ⟨⟨z, hclose a.1.1 haN hau z hz⟩, hz, rfl⟩
    have hb := identification_degree_balance J SC a
    rw [hf] at hb
    have hi : (J.neighborSet a.1 ∩ SC).ncard ≤ SC.ncard :=
      Set.ncard_le_ncard Set.inter_subset_right
    change k - s + 2 ≤ ((identificationGraph J SC).neighborSet (some a)).ncard
    by_cases he : ∃ z ∈ SC, J.Adj a.1 z
    · have hbit : collapsedNeighborCount J SC a.1 = 1 := by
        unfold collapsedNeighborCount
        exact ite_eq_left he
      rw [hbit] at hb
      omega
    · have hem : J.neighborSet a.1 ∩ SC = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro z ⟨ez, hz⟩
        exact he ⟨z, hz, ez⟩
      have hbit : collapsedNeighborCount J SC a.1 = 0 := by
        unfold collapsedNeighborCount
        exact ite_eq_right he
      rw [hem, Set.ncard_empty, hbit] at hb
      omega

theorem biclique_third_quotient_family_from_smaller_IH [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hAB : Disjoint A B) (hx : x ∈ B) (hy : y ∉ A ∪ B)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ (A ∪ B)).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (hcase : BicliqueThirdRootCase G A B y u C)
    (hBtouch : (bicliqueThirdCollapse G A B x y C).Nonempty)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths
      (regionIdentificationGraph G (bicliqueThirdRetained G A B y u C)
        (bicliqueThirdCollapse G A B x y C)) none
      (some (regionRetainedVertex (bicliqueThirdRetained G A B y u C)
        (bicliqueThirdCollapse G A B x y C) (biclique_third_disjoint G A B x y u C hAB hcase)
        ⟨u, Or.inr rfl⟩)) (k - s + 1) := by
  classical
  let N := bicliqueThirdRetained G A B y u C
  let S := bicliqueThirdCollapse G A B x y C
  let : Fintype (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S}) :=
    bicliqueThirdFintype G A B x y u C
  have hr := biclique_third_quotient_rooted G A B x y u s k C hG hAB hx hs hsk hNx hNy
    hcap hd hcase hBtouch
  have hn := biclique_third_strict_order G A B x y u s C hAB hy hs hB hcase
  have hn' : Fintype.card (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S}) <
      Fintype.card V := by simpa only [Fintype.card_eq_nat_card] using hn
  have hdegree := biclique_third_nonroot_degree G A B x y u s k C hx hs hB (by omega)
    hNx hNy hAB hcase hd
  have hdegree' : NonrootDegreeAtLeast (regionIdentificationGraph G N S) none
      (some (regionRetainedVertex N S (biclique_third_disjoint G A B x y u C hAB hcase)
        ⟨u, Or.inr rfl⟩)) (k - s + 1 + 1) := by
    simpa only [Nat.add_assoc] using hdegree
  exact ih (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S})
    (regionIdentificationGraph G N S) none
    (some (regionRetainedVertex N S (biclique_third_disjoint G A B x y u C hAB hcase)
      ⟨u, Or.inr rfl⟩)) (k - s + 1) hn' (by omega) hr hdegree'

#print axioms bicliqueThirdFintype
#print axioms biclique_third_quotient_rooted
#print axioms biclique_third_strict_order
#print axioms biclique_third_order_internal
#print axioms biclique_third_order_external
#print axioms biclique_third_nonroot_degree
#print axioms biclique_third_quotient_family_from_smaller_IH
end TaskH.Gao
