import Research.TaskH.Gao.CasebiFeasibleFirstPart
import Research.TaskH.Gao.CliqueEmptyInductionStep

/-! Actual second-side loss and the real-x empty-boundary branch. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_fragment_nonroot_interior (G : SimpleGraph V) (Q : Set V)
    (C : (G.induce Qᶜ).ConnectedComponent) (I : Set C.supp) (b : C.supp)
    (v : componentRegion C (fragmentBlock I b)) (hvb : v.1 ≠ componentVertex C b) :
    ∃ w ∈ I, componentVertex C w = v.1 := by
  obtain ⟨w, hw, he⟩ := v.2
  rcases hw with hwb | hwI
  · exact False.elim (hvb (he.symm.trans (congrArg (componentVertex C) hwb)))
  · exact ⟨w, hwI, he⟩

theorem casebi_second_part_quotient_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1)
    (hs : 1 ≤ s) (hsk : s ≤ k) (hd : NonrootDegreeAtLeast G x y (k + 1))
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) (yr : C.supp)
    (hY : componentVertex C yr = y) (I : Set C.supp) (b : C.supp)
    (hT : TerminalFragment C.toSimpleGraph I b) (hyI : yr ∉ I)
    (hnoA : ∀ w ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C w) a)
    (hcase : 2 ≤ s ∨ ∀ w ∈ I, ¬G.Adj (componentVertex C w) x)
    (v : componentRegion C (fragmentBlock I b)) (hvb : v.1 ≠ componentVertex C b) :
    k - s + 2 ≤
      ((regionIdentificationGraph G (componentRegion C (fragmentBlock I b))
        (cliqueBlockBoundary G (componentRegion C (fragmentBlock I b)) B x (componentVertex C b))).neighborSet
        (some (regionRetainedVertex (componentRegion C (fragmentBlock I b))
          (cliqueBlockBoundary G (componentRegion C (fragmentBlock I b)) B x (componentVertex C b))
          (cliqueBlock_boundary_disjoint G (componentRegion C (fragmentBlock I b)) B x
            (componentVertex C b) (Set.disjoint_left.mpr
              (fun _ hzD hzB => Set.disjoint_left.mp
                (componentRegion_disjoint C (fragmentBlock I b)) hzD (Or.inr hzB)))) v))).ncard := by
  classical
  let D := componentRegion C (fragmentBlock I b)
  let S := cliqueBlockBoundary G D B x (componentVertex C b)
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  have hDB : Disjoint D B := Set.disjoint_left.mpr
    (fun _ hzD hzB => Set.disjoint_left.mp hDQ hzD (Or.inr hzB))
  have hDS : Disjoint D S := cliqueBlock_boundary_disjoint G D B x (componentVertex C b) hDB
  obtain ⟨w, hwI, he⟩ := casebi_fragment_nonroot_interior G (A ∪ B) C I b v hvb
  have hvNoA : ∀ a ∈ A, ¬G.Adj v.1 a := by
    intro a ha eva
    exact hnoA w hwI a ha (Eq.mpr (congrArg (fun z : V => G.Adj z a) he) eva)
  have hvx : v.1 ≠ x := fun he => Set.disjoint_left.mp hDQ v.2
    (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inr hmax.1.2.2.1))
  have hBy : y ∈ D → y = componentVertex C b := by
    rw [← hY]; exact component_fragment_y_boundary C I b yr hyI
  have hvy : v.1 ≠ y := fun he => hvb
    (he.trans (hBy (Eq.mp (congrArg (fun z : V => z ∈ D) he) v.2)))
  have hout : v.1 ∉ (A ∪ B) ∪ {y} := by
    rintro (hz | he)
    · exact Set.disjoint_left.mp hDQ v.2 hz
    · exact hvy he
  have hp := disjoint_region_neighbor_partition G D (A ∪ B) hDQ v.1
    (component_fragment_original_cover C I b hT v.1 v.2 hvb)
  have hq := regionIdentification_neighbor_ncard G D S hDS v
  have hOrig := hd v.1 hvx hvy
  have heq : G.neighborSet v.1 ∩ (A ∪ B) = G.neighborSet v.1 ∩ B := by
    ext z
    constructor
    · rintro ⟨evz, hzA | hzB⟩
      · exact False.elim (hvNoA z hzA evz)
      · exact ⟨evz, hzB⟩
    · rintro ⟨evz, hzB⟩; exact ⟨evz, Or.inr hzB⟩
  rw [heq] at hp
  have hcap := casebi_lexmax_second_neighbor_cap G x y A B hmax v.1 hout
  change k - s + 2 ≤ ((regionIdentificationGraph G D S).neighborSet
    (some (regionRetainedVertex D S hDS v))).ncard
  by_cases ht : ∃ z ∈ S, G.Adj v.1 z
  · have hbit : collapsedNeighborCount G S v.1 = 1 := by
      unfold collapsedNeighborCount; exact ite_eq_left ht
    rw [hq, hbit]
    omega
  · have hbit : collapsedNeighborCount G S v.1 = 0 := by
      unfold collapsedNeighborCount; exact ite_eq_right ht
    have hsub : G.neighborSet v.1 ∩ B ⊆ {x} := by
      rintro z ⟨evz, hzB⟩
      by_contra hzx
      exact ht ⟨z, ⟨hzB, hzx, v.1, v.2, hvb, evz⟩, evz⟩
    have hsmall : (G.neighborSet v.1 ∩ B).ncard ≤ 1 := by
      simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub
    rw [hq, hbit]
    rcases hcase with hs2 | hnoX
    · omega
    · have hvNoX : ¬G.Adj v.1 x := fun evx => hnoX w hwI
        (Eq.mpr (congrArg (fun z : V => G.Adj z x) he) evx)
      have hem : G.neighborSet v.1 ∩ B = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro z ⟨evz, hzB⟩
        have hez : z = x := hsub ⟨evz, hzB⟩
        exact hvNoX (Eq.mp (congrArg (fun z : V => G.Adj v.1 z) hez) evz)
      rw [hem, Set.ncard_empty] at hp
      omega

theorem casebi_empty_second_boundary_family [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (r + 1) → HasAdmissiblePaths J a d r)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b) (hyI : yr ∉ I)
    (hS : cliqueBlockBoundary G (componentRegion C (fragmentBlock I b)) B x
      (componentVertex C b) = ∅) : HasAdmissiblePaths G x y k := by
  subst y
  classical
  let D := componentRegion C (fragmentBlock I b)
  let : Fintype D := Fintype.ofFinite _
  let : Fintype (fragmentBlock I b) := Fintype.ofFinite _
  let : Fintype (D ∪ {x} : Set V) := Fintype.ofFinite _
  let br : D := ⟨componentVertex C b, b, Or.inl rfl, rfl⟩
  have hI := casebi_terminal_interior_two G A B x (componentVertex C yr) s k hmax hBs hk
    htri hquad hd hno C yr rfl I b hT hyI
  have hD : TwoConnected (G.induce D) := twoConnected_of_graphIso
    (C.toSimpleGraph.induce (fragmentBlock I b)) (G.induce D)
    (componentRegionGraphIso C (fragmentBlock I b))
    (terminalFragment_twoConnected C.toSimpleGraph I b hT hI)
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  have hnoA := casebi_feasible_no_first_part G A B x (componentVertex C yr) s k hmax hBs hk
    hG htri hquad hd hno ih C yr rfl I b hT hyI
  have hcover : ∀ v ∈ D, v ≠ componentVertex C b → ∀ z, G.Adj v z → z ∈ D ∨ z = x := by
    intro v hv hvb z evz
    rcases component_fragment_original_cover C I b hT v hv hvb z evz with hzD | hzA | hzB
    · exact Or.inl hzD
    · obtain ⟨w, hwI, he⟩ := casebi_fragment_nonroot_interior G (A ∪ B) C I b ⟨v, hv⟩ hvb
      exact False.elim (hnoA w hwI z hzA
        (Eq.mpr (congrArg (fun v : V => G.Adj v z) he) evz))
    · by_cases hzx : z = x
      · exact Or.inr hzx
      · have hzS : z ∈ cliqueBlockBoundary G D B x (componentVertex C b) := ⟨hzB, hzx, v, hv, hvb, evz⟩
        rw [hS] at hzS
        exact False.elim hzS
  have hQcard : 3 ≤ (A ∪ B).ncard := by
    have hparts : (A ∪ B).ncard = A.ncard + B.ncard := Set.ncard_union_eq hmax.1.1
    have hB2 := hmax.1.2.2.2.2.1
    have hBA := hmax.1.2.2.2.2.2
    omega
  have hempty : cliqueBlockBoundary G D (A ∪ B) x (componentVertex C b) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨_hzQ, hzx, v, hv, hvb, evz⟩
    rcases hcover v hv hvb z evz with hzD | he
    · exact Set.disjoint_left.mp hDQ hzD _hzQ
    · exact hzx he
  have hcoverQ : ∀ v ∈ D, v ≠ componentVertex C b → ∀ z, G.Adj v z → z ∈ D ∨ z ∈ A ∪ B :=
    component_fragment_original_cover C I b hT
  have hBy : componentVertex C yr ∈ D → componentVertex C yr = br.1 :=
    component_fragment_y_boundary C I b yr hyI
  obtain ⟨R, hR, hRQ, hRD⟩ := terminal_component_original_tail C I b yr hT hyI
  exact clique_empty_branch_from_smaller_IH G D (A ∪ B) x (componentVertex C yr) k br
    hG hD hDQ (Or.inr hmax.1.2.2.1) hQcard (by omega) hBy hd hempty hcoverQ R hR
    (fun hxR => hRQ x hxR (Or.inr hmax.1.2.2.1)) hRD ih

#print axioms casebi_fragment_nonroot_interior
#print axioms casebi_second_part_quotient_degree
#print axioms casebi_empty_second_boundary_family
end TaskH.Gao
