import Research.TaskH.Gao.BicliqueSingletonFirstGeometry
import Research.TaskH.Gao.Challenge

/-! The original k+1 degree becomes k-s+3 in the actual boundary quotient. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem biclique_first_nonroot_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hx : x ∈ B) (hy : y ∉ A ∪ B)
    (hs : 1 ≤ s) (hsk : s ≤ k) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ¬∃ a ∈ A, ∃ d : C.supp, G.Adj a d.1.1)
    (hu : u ∈ singletonG1Boundary G (bicliqueSingletonCore A B y) C)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast
      (boundaryQuotient G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u) none
      (some (boundaryRetainedRoot G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u
        (by rw [singleton_g1_full_boundary]; exact hu))) (k - s + 3) := by
  classical
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  have hvB : u ∈ equalBranchBoundary G R := by rw [singleton_g1_full_boundary]; exact hu
  have hbud := biclique_first_two_boundary_forces_s G A B x y s C hG hx hy hs hB hNx hNy hnoA
  have hs2 : 2 ≤ s := hbud.1
  have hbcard : (singletonG1Boundary G K C).ncard ≤ s := hbud.2.2
  have hc := biclique_first_collapse_ncard G K C u
  rw [Set.ncard_sdiff_singleton_of_mem hu] at hc
  change (boundaryCollapse G R u).ncard =
    (singletonG1Boundary G K C).ncard - 1 at hc
  have hS : (boundaryCollapse G R u).ncard ≤ s - 1 := by omega
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
    have hf : ((G.induce (boundaryDomain G R)).neighborSet a.1).ncard =
        (G.neighborSet a.1.1).ncard :=
      (equalBranchRegion_neighbor_ncard G R ⟨a.1.1, haK, haC⟩).symm
    have hb := identification_degree_balance (G.induce (boundaryDomain G R))
      (boundaryCollapse G R u) a
    rw [hf] at hb
    have hi : (((G.induce (boundaryDomain G R)).neighborSet a.1) ∩ boundaryCollapse G R u).ncard ≤
        (boundaryCollapse G R u).ncard := Set.ncard_le_ncard Set.inter_subset_right
    change k - s + 3 ≤
      ((identificationGraph (G.induce (boundaryDomain G R)) (boundaryCollapse G R u)).neighborSet
        (some a)).ncard
    by_cases he : ∃ z ∈ boundaryCollapse G R u, (G.induce (boundaryDomain G R)).Adj a.1 z
    · have hbit : collapsedNeighborCount (G.induce (boundaryDomain G R))
          (boundaryCollapse G R u) a.1 = 1 := by
        unfold collapsedNeighborCount
        exact ite_eq_left he
      rw [hbit] at hb
      omega
    · have hem : ((G.induce (boundaryDomain G R)).neighborSet a.1 ∩ boundaryCollapse G R u) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro z ⟨ez, hz⟩
        exact he ⟨z, hz, ez⟩
      have hbit : collapsedNeighborCount (G.induce (boundaryDomain G R))
          (boundaryCollapse G R u) a.1 = 0 := by
        unfold collapsedNeighborCount
        exact ite_eq_right he
      rw [hem, Set.ncard_empty, hbit] at hb
      omega

theorem biclique_first_family_from_smaller_IH [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y u : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (hG : TwoConnected G) (hx : x ∈ B) (hy : y ∉ A ∪ B)
    (hs : 1 ≤ s) (hsk : s ≤ k) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ¬∃ a ∈ A, ∃ d : C.supp, G.Adj a d.1.1)
    (hu : u ∈ singletonG1Boundary G (bicliqueSingletonCore A B y) C)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths
      (boundaryQuotient G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u) none
      (some (boundaryRetainedRoot G (singletonG1Vertices G (bicliqueSingletonCore A B y) C) u
        (by rw [singleton_g1_full_boundary]; exact hu))) (k - s + 2) := by
  classical
  let K := bicliqueSingletonCore A B y
  let R := singletonG1Vertices G K C
  let : Fintype (IdentificationVertex (boundaryCollapse G R u)) := singletonG1Fintype G K C u
  have hK := biclique_first_core_card A B y s hy hs hB
  change 3 ≤ K.ncard at hK
  have hroot := singleton_g1_rooted G K C x u hG (Or.inl (Or.inr hx)) (by omega) hu
  have hdegree := biclique_first_nonroot_degree G A B x y u s k C hG hx hy hs hsk hB hNx hNy hnoA hu hd
  have hn := biclique_first_strict_order G A B y u s C hy hs hB hu
  have hn' : Fintype.card (IdentificationVertex (boundaryCollapse G R u)) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hn
  have hdegree' : NonrootDegreeAtLeast (boundaryQuotient G R u) none
      (some (boundaryRetainedRoot G R u (by rw [singleton_g1_full_boundary]; exact hu)))
      (k - s + 2 + 1) := by
    simpa only [Nat.add_assoc] using hdegree
  exact ih (IdentificationVertex (boundaryCollapse G R u)) (boundaryQuotient G R u) none
    (some (boundaryRetainedRoot G R u (by rw [singleton_g1_full_boundary]; exact hu)))
    (k - s + 2) hn' (by omega) hroot hdegree'

#print axioms biclique_first_nonroot_degree
#print axioms biclique_first_family_from_smaller_IH
end TaskH.Gao
