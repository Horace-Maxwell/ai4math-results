import Research.TaskH.Gao.BicliqueTerminalGeometry
import Research.TaskH.Gao.IdentificationDegree
import Research.TaskH.Gao.Challenge

/-! Actual G4 rootedness, exact original-neighbor degree, strict cardinal IH. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

@[instance_reducible]
noncomputable def g4Fintype [Fintype V] (G : SimpleGraph V) (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) :
    Fintype (IdentificationVertex {z : (g4Block G A B y C I b ∪ g4Boundary G A B x y C I : Set V) |
      z.1 ∈ g4Boundary G A B x y C I}) := Fintype.ofFinite _

theorem g4_quotient_rooted [Fintype V] (G : SimpleGraph V) (A B : Set V) (x y : V)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hG : TwoConnected G) (hx : x ∈ B)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ∀ d ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C d) a) :
    @RootedTwoConnected (IdentificationVertex
      {z : (g4Block G A B y C I b ∪ g4Boundary G A B x y C I : Set V) |
        z.1 ∈ g4Boundary G A B x y C I}) (g4Fintype G A B x y C I b)
      (regionIdentificationGraph G (g4Block G A B y C I b) (g4Boundary G A B x y C I)) none
      (some (regionRetainedVertex _ _ (g4_block_boundary_disjoint G A B x y C I b)
        ⟨componentVertex C b, g4_root_mem G A B y C I b⟩)) := by
  classical
  let N := g4Block G A B y C I b
  let S := g4Boundary G A B x y C I
  let : Fintype (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S}) := g4Fintype G A B x y C I b
  exact rootRegion_quotient_rooted G N S (g4_block_boundary_disjoint G A B x y C I b)
    ⟨componentVertex C b, g4_root_mem G A B y C I b⟩
    (g4_boundary_nonempty G A B x y C I b hT hG hx hNx hNy hnoA)
    (g4_block_connected G A B y C I b hT) (g4_block_card_ge_two G A B y C I b hT)
    (g4_full_neighbor_cover G A B x y C I b hT hNx hNy hnoA) hG

theorem g4_strict_original_order [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (x y : V) (s : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hy : y ∉ A ∪ B) (hs : 1 ≤ s)
    (hB : B.ncard = s + 1) :
    Nat.card (IdentificationVertex
      {z : (g4Block G A B y C I b ∪ g4Boundary G A B x y C I : Set V) |
        z.1 ∈ g4Boundary G A B x y C I}) < Nat.card V := by
  let N := g4Block G A B y C I b
  let S := g4Boundary G A B x y C I
  have hn := Set.ncard_le_card (N ∪ bicliqueSingletonCore A B y)
  rw [Set.ncard_union_eq (g4_block_disjoint_core G A B y C I b)] at hn
  change N.ncard + (bicliqueSingletonCore A B y).ncard ≤ Nat.card V at hn
  have hK := biclique_first_core_card A B y s hy hs hB
  rw [regionIdentification_card N S (g4_block_boundary_disjoint G A B x y C I b)]
  omega

theorem g4_original_nonroot_degree [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hx : x ∈ B) (hs : 1 ≤ s) (hsk : s ≤ k) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ∀ d ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C d) a)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast
      (regionIdentificationGraph G (g4Block G A B y C I b) (g4Boundary G A B x y C I)) none
      (some (regionRetainedVertex _ _ (g4_block_boundary_disjoint G A B x y C I b)
        ⟨componentVertex C b, g4_root_mem G A B y C I b⟩)) (k - s + 2) := by
  classical
  let N := g4Block G A B y C I b
  let S := g4Boundary G A B x y C I
  let T := N ∪ S
  let J := G.induce T
  let SC : Set T := {z | z.1 ∈ S}
  have hclose := g4_full_neighbor_cover G A B x y C I b hT hNx hNy hnoA
  have hSc : SC.ncard = S.ncard := by
    apply Set.ncard_congr (fun z _ => z.1)
    · intro z hz; exact hz
    · intro a d _ _ he; exact Subtype.ext he
    · intro z hz; exact ⟨⟨z, Or.inr hz⟩, hz, rfl⟩
  have hS := g4_boundary_card G A B x y s C I hx hB
  change S.ncard ≤ s at hS
  intro q hqn hqb
  cases q with
  | none => exact False.elim (hqn rfl)
  | some a =>
    have hab : a.1.1 ≠ componentVertex C b := by
      intro he
      exact hqb (congrArg Option.some (Subtype.ext (Subtype.ext he)))
    have haN : a.1.1 ∈ N := a.1.2.elim id (fun h => False.elim (a.2 h))
    have haK : a.1.1 ∉ bicliqueSingletonCore A B y :=
      Set.disjoint_left.mp (g4_block_disjoint_core G A B y C I b) haN
    have hax : a.1.1 ≠ x := fun he => haK
      (Eq.mpr (congrArg (fun v : V => v ∈ bicliqueSingletonCore A B y) he) (Or.inl (Or.inr hx)))
    have hay : a.1.1 ≠ y := fun he => haK
      (Eq.mpr (congrArg (fun v : V => v ∈ bicliqueSingletonCore A B y) he) (Or.inr rfl))
    have hOrig := hd a.1.1 hax hay
    have hf : (J.neighborSet a.1).ncard = (G.neighborSet a.1.1).ncard := by
      apply Set.ncard_congr (fun z _ => z.1)
      · intro z hz; exact hz
      · intro z w _ _ he; exact Subtype.ext he
      · intro z hz; exact ⟨⟨z, hclose a.1.1 haN hab z hz⟩, hz, rfl⟩
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

theorem g4_family_from_strict_IH [Fintype V] (G : SimpleGraph V) (A B : Set V)
    (x y : V) (s k : ℕ)
    (C : (G.induce (bicliqueSingletonCore A B y)ᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hG : TwoConnected G) (hx : x ∈ B) (hy : y ∉ A ∪ B)
    (hs : 1 ≤ s) (hsk : s ≤ k - 2) (hB : B.ncard = s + 1)
    (hNx : G.neighborSet x = A) (hNy : G.neighborSet y = A)
    (hnoA : ∀ d ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C d) a)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a b : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a b →
      NonrootDegreeAtLeast J a b (r + 1) → HasAdmissiblePaths J a b r) :
    HasAdmissiblePaths
      (regionIdentificationGraph G (g4Block G A B y C I b) (g4Boundary G A B x y C I)) none
      (some (regionRetainedVertex _ _ (g4_block_boundary_disjoint G A B x y C I b)
        ⟨componentVertex C b, g4_root_mem G A B y C I b⟩)) (k - s + 1) := by
  classical
  let N := g4Block G A B y C I b
  let S := g4Boundary G A B x y C I
  let : Fintype (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S}) := g4Fintype G A B x y C I b
  have hr := g4_quotient_rooted G A B x y C I b hT hG hx hNx hNy hnoA
  have hn := g4_strict_original_order G A B x y s C I b hy hs hB
  have hn' : Fintype.card (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S}) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hn
  have hdegree := g4_original_nonroot_degree G A B x y s k C I b hT hx hs (by omega)
    hB hNx hNy hnoA hd
  have hdegree' : NonrootDegreeAtLeast (regionIdentificationGraph G N S) none
      (some (regionRetainedVertex N S (g4_block_boundary_disjoint G A B x y C I b)
        ⟨componentVertex C b, g4_root_mem G A B y C I b⟩)) (k - s + 1 + 1) := by
    simpa only [Nat.add_assoc] using hdegree
  exact ih (IdentificationVertex {z : (N ∪ S : Set V) | z.1 ∈ S})
    (regionIdentificationGraph G N S) none
    (some (regionRetainedVertex N S (g4_block_boundary_disjoint G A B x y C I b)
      ⟨componentVertex C b, g4_root_mem G A B y C I b⟩)) (k - s + 1) hn' (by omega) hr hdegree'

#print axioms g4Fintype
#print axioms g4_quotient_rooted
#print axioms g4_strict_original_order
#print axioms g4_original_nonroot_degree
#print axioms g4_family_from_strict_IH
end TaskH.Gao
