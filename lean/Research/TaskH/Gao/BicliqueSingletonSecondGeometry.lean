import Research.TaskH.Gao.BicliqueSingletonFirstGeometry
import Research.TaskH.Gao.IdentificationDegree

/-! Primary591–596, with the actual per-vertex cap from casebi 2(a). -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem biclique_maximal_second_part_neighbor_cap [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s : ℕ)
    (hAB : Disjoint A B) (hc : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hx : x ∈ B) (hy : y ∉ A ∪ B) (hB : B.ncard = s + 1)
    (hmax : ∀ L M : Set V, Disjoint L M →
      (∀ a ∈ L, ∀ b ∈ M, G.Adj a b) → x ∈ M → y ∉ L ∪ M →
      2 ≤ M.ncard → M.ncard ≤ L.ncard → M.ncard ≤ B.ncard)
    (d : V) (hd : d ∉ bicliqueSingletonCore A B y) :
    (G.neighborSet d ∩ A).ncard ≤ s + 1 := by
  classical
  by_contra hn
  let L := G.neighborSet d ∩ A
  let M := insert d B
  have hL : s + 2 ≤ L.ncard := by
    change ¬L.ncard ≤ s + 1 at hn
    omega
  have hdB : d ∉ B := fun h => hd (Or.inl (Or.inr h))
  have hM : M.ncard = s + 2 := by
    change (insert d B).ncard = s + 2
    rw [Set.ncard_insert_of_notMem hdB, hB]
  have hdis : Disjoint L M := by
    apply Set.disjoint_left.mpr
    intro z hzL hzM
    rcases Set.mem_insert_iff.mp hzM with he | hzB
    · have hdA : d ∈ A := Eq.mp (congrArg (fun v : V => v ∈ A) he) hzL.2
      exact hd (Or.inl (Or.inl hdA))
    · exact Set.disjoint_left.mp hAB hzL.2 hzB
  have hcross : ∀ a ∈ L, ∀ b ∈ M, G.Adj a b := by
    intro a ha b hb
    rcases Set.mem_insert_iff.mp hb with he | hbB
    · exact Eq.mpr (congrArg (fun v : V => G.Adj a v) he) ha.1.symm
    · exact hc a ha.2 b hbB
  have hyo : y ∉ L ∪ M := by
    rintro (hyL | hyM)
    · exact hy (Or.inl hyL.2)
    · rcases Set.mem_insert_iff.mp hyM with he | hyB
      · exact hd (Eq.mp (congrArg (fun v : V => v ∈ bicliqueSingletonCore A B y) he)
          (Or.inr rfl))
      · exact hy (Or.inr hyB)
  have hbound := hmax L M hdis hcross (Set.mem_insert_of_mem d hx) hyo
    (by omega) (by omega)
  omega

theorem biclique_second_boundary_subset (G : SimpleGraph V)
    (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoB : ¬∃ b ∈ B \ {x}, ∃ d : C.supp, G.Adj b d.1.1) :
    singletonG1Boundary G (bicliqueSingletonCore A B y) C ⊆ A := by
  rintro a ⟨haK, d, eda⟩
  have hay : a ≠ y := by
    intro he
    have ey : G.Adj y d.1.1 := Eq.mp
      (congrArg (fun z : V => G.Adj z d.1.1) he) eda.symm
    have hdA : d.1.1 ∈ A :=
      Eq.mp (congrArg (fun S : Set V => d.1.1 ∈ S) hNy) ey
    exact d.1.2 (Or.inl (Or.inl hdA))
  have hax : a ≠ x := by
    intro he
    have ex : G.Adj x d.1.1 := Eq.mp
      (congrArg (fun z : V => G.Adj z d.1.1) he) eda.symm
    have hdA : d.1.1 ∈ A :=
      Eq.mp (congrArg (fun S : Set V => d.1.1 ∈ S) hNx) ex
    exact d.1.2 (Or.inl (Or.inl hdA))
  rcases haK with (ha | ha) | ha
  · exact ha
  · exact False.elim (hnoB ⟨a, ⟨ha, hax⟩, d, eda.symm⟩)
  · exact False.elim (hay ha)

theorem biclique_second_size_cases (A : Set V) (s : ℕ)
    (hA : s + 1 ≤ A.ncard) :
    ((if A.ncard = s + 1 then 1 else 0) = 0 ∧ s + 2 ≤ A.ncard) ∨
      ((if A.ncard = s + 1 then 1 else 0) = 1 ∧ A.ncard = s + 1) := by
  classical
  by_cases he : A.ncard = s + 1
  · exact Or.inr ⟨ite_eq_left he, he⟩
  · exact Or.inl ⟨ite_eq_right he, by omega⟩

theorem biclique_second_nonroot_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V) (s k eps : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hx : x ∈ B) (hs : 1 ≤ s) (hsk : s ≤ k)
    (heps : (eps = 0 ∧ s + 2 ≤ A.ncard) ∨ (eps = 1 ∧ A.ncard = s + 1))
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoB : ¬∃ b ∈ B \ {x}, ∃ d : C.supp, G.Adj b d.1.1)
    (hu : u ∈ singletonG1Boundary G (bicliqueSingletonCore A B y) C)
    (hcap : ∀ d : C.supp, (G.neighborSet d.1.1 ∩ A).ncard ≤ s + 1)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast
      (boundaryQuotient G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u) none
      (some (boundaryRetainedRoot G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u
        (by rw [singleton_g1_full_boundary]; exact hu))) (k - s + 1 + eps) := by
  classical
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  let J := G.induce (boundaryDomain G R)
  let S := boundaryCollapse G R u
  have hsub := biclique_second_boundary_subset G A B x y C hNx hNy hnoB
  have hE : (singletonG1Boundary G K C).ncard ≤ A.ncard := Set.ncard_le_ncard hsub
  have hScard := biclique_first_collapse_ncard G K C u
  rw [Set.ncard_sdiff_singleton_of_mem hu] at hScard
  intro q hqn hqu
  cases q with
  | none => exact False.elim (hqn rfl)
  | some a =>
    have hau : a.1.1 ≠ u := by
      intro he
      exact hqu (congrArg Option.some (Subtype.ext (Subtype.ext he)))
    have haR : a.1.1 ∈ R := by
      rcases a.1.2 with ha | ha
      · exact ha
      · exact False.elim (a.2 ⟨ha, hau⟩)
    obtain ⟨haK, haC⟩ := haR
    have hax : a.1.1 ≠ x := fun he => haK
      (Eq.mpr (congrArg (fun z : V => z ∈ K) he) (Or.inl (Or.inr hx)))
    have hay : a.1.1 ≠ y := fun he => haK
      (Eq.mpr (congrArg (fun z : V => z ∈ K) he) (Or.inr rfl))
    have hOrig := hd a.1.1 hax hay
    have hf : (J.neighborSet a.1).ncard = (G.neighborSet a.1.1).ncard :=
      (equalBranchRegion_neighbor_ncard G R ⟨a.1.1, haK, haC⟩).symm
    have hb := identification_degree_balance J S a
    rw [hf] at hb
    have hiS : (J.neighborSet a.1 ∩ S).ncard ≤ S.ncard :=
      Set.ncard_le_ncard Set.inter_subset_right
    have hiA : (J.neighborSet a.1 ∩ S).ncard ≤ s + 1 := by
      have himage : (Subtype.val '' (J.neighborSet a.1 ∩ S)) ⊆
          G.neighborSet a.1.1 ∩ A := by
        rintro z ⟨b, hb, rfl⟩
        have hbE := hb.2.1
        rw [singleton_g1_full_boundary] at hbE
        exact ⟨hb.1, hsub hbE⟩
      have hh := Set.ncard_le_ncard himage
      rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hh
      exact le_trans hh (hcap ⟨⟨a.1.1, haK⟩, haC⟩)
    have hi : (J.neighborSet a.1 ∩ S).ncard ≤ s + 1 - eps := by
      rcases heps with ⟨he, _hA⟩ | ⟨he, hA⟩
      · subst eps
        omega
      · subst eps
        change S.ncard =
          (singletonG1Boundary G K C).ncard - 1 at hScard
        omega
    have heps01 : eps = 0 ∨ eps = 1 := heps.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    change k - s + 1 + eps ≤ ((identificationGraph J S).neighborSet (some a)).ncard
    by_cases he : ∃ z ∈ S, J.Adj a.1 z
    · have hbit : collapsedNeighborCount J S a.1 = 1 := by
        unfold collapsedNeighborCount
        exact ite_eq_left he
      rw [hbit] at hb
      omega
    · have hem : J.neighborSet a.1 ∩ S = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro z ⟨ez, hz⟩
        exact he ⟨z, hz, ez⟩
      have hbit : collapsedNeighborCount J S a.1 = 0 := by
        unfold collapsedNeighborCount
        exact ite_eq_right he
      rw [hem, Set.ncard_empty, hbit] at hb
      omega

#print axioms biclique_maximal_second_part_neighbor_cap
#print axioms biclique_second_boundary_subset
#print axioms biclique_second_size_cases
#print axioms biclique_second_nonroot_degree
end TaskH.Gao
