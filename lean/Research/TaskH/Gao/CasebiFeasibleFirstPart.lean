import Research.TaskH.Gao.CasebiFeasibleTerminalBlock
import Research.TaskH.Gao.CliqueBoundaryRooted
import Research.TaskH.Gao.IdentificationFamilyLift

/-! The actual feasible block cannot attach to Q1; every child datum is derived. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_first_part_quotient_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hsk : s ≤ k)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) (yr : C.supp)
    (hY : componentVertex C yr = y) (I : Set C.supp) (b : C.supp)
    (hT : TerminalFragment C.toSimpleGraph I b) (hyI : yr ∉ I)
    (v : componentRegion C (fragmentBlock I b)) (hvb : v.1 ≠ componentVertex C b) :
    k - s + 1 ≤
      ((regionIdentificationGraph G (componentRegion C (fragmentBlock I b))
        (cliqueBlockBoundary G (componentRegion C (fragmentBlock I b)) A x (componentVertex C b))).neighborSet
        (some (regionRetainedVertex (componentRegion C (fragmentBlock I b))
          (cliqueBlockBoundary G (componentRegion C (fragmentBlock I b)) A x (componentVertex C b))
          (cliqueBlock_boundary_disjoint G (componentRegion C (fragmentBlock I b)) A x
            (componentVertex C b) (Set.disjoint_left.mpr
              (fun _ hzD hzA => Set.disjoint_left.mp
                (componentRegion_disjoint C (fragmentBlock I b)) hzD (Or.inl hzA)))) v))).ncard := by
  classical
  let D := componentRegion C (fragmentBlock I b)
  let S := cliqueBlockBoundary G D A x (componentVertex C b)
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  have hDA : Disjoint D A := Set.disjoint_left.mpr
    (fun _ hzD hzA => Set.disjoint_left.mp hDQ hzD (Or.inl hzA))
  have hDS : Disjoint D S := cliqueBlock_boundary_disjoint G D A x (componentVertex C b) hDA
  have hvx : v.1 ≠ x := fun he => Set.disjoint_left.mp hDQ v.2
    (Eq.mpr (congrArg (fun z : V => z ∈ A ∪ B) he) (Or.inr hmax.1.2.2.1))
  have hBy : y ∈ D → y = componentVertex C b := by
    rw [← hY]
    exact component_fragment_y_boundary C I b yr hyI
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
  have htouch : (∃ z ∈ S, G.Adj v.1 z) ↔ ∃ z ∈ A, G.Adj v.1 z := by
    constructor
    · rintro ⟨z, hz, evz⟩; exact ⟨z, hz.1, evz⟩
    · rintro ⟨z, hzA, evz⟩
      have hzx : z ≠ x := fun he => Set.disjoint_left.mp hmax.1.1 hzA
        (Eq.mpr (congrArg (fun z : V => z ∈ B) he) hmax.1.2.2.1)
      exact ⟨z, ⟨hzA, hzx, v.1, v.2, hvb, evz⟩, evz⟩
  by_cases hA : ∃ z ∈ A, G.Adj v.1 z
  · have hbit : collapsedNeighborCount G S v.1 = 1 := by
      unfold collapsedNeighborCount
      exact ite_eq_left (htouch.mpr hA)
    have hcap := casebi_lexmax_total_neighbor_cap G x y A B hmax htri hquad v.1 hout
    change k - s + 1 ≤ ((regionIdentificationGraph G D S).neighborSet
      (some (regionRetainedVertex D S hDS v))).ncard
    rw [hq, hbit]
    omega
  · have hbit : collapsedNeighborCount G S v.1 = 0 := by
      unfold collapsedNeighborCount
      exact ite_eq_right (fun hh => hA (htouch.mp hh))
    have heq : G.neighborSet v.1 ∩ (A ∪ B) = G.neighborSet v.1 ∩ B := by
      ext z
      constructor
      · rintro ⟨evz, hzA | hzB⟩
        · exact False.elim (hA ⟨z, hzA, evz⟩)
        · exact ⟨evz, hzB⟩
      · rintro ⟨evz, hzB⟩; exact ⟨evz, Or.inr hzB⟩
    rw [heq] at hp
    have hcap := casebi_lexmax_second_neighbor_cap G x y A B hmax v.1 hout
    change k - s + 1 ≤ ((regionIdentificationGraph G D S).neighborSet
      (some (regionRetainedVertex D S hDS v))).ncard
    rw [hq, hbit]
    omega

theorem casebi_feasible_first_part_family [Fintype V] (G : SimpleGraph V)
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
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hyI : yr ∉ I)
    (hS : (cliqueBlockBoundary G (componentRegion C (fragmentBlock I b)) A x
      (componentVertex C b)).Nonempty) : HasAdmissiblePaths G x y k := by
  subst y
  classical
  let D := componentRegion C (fragmentBlock I b)
  let S := cliqueBlockBoundary G D A x (componentVertex C b)
  let m := k - s
  let : Fintype D := Fintype.ofFinite _
  let : Fintype (fragmentBlock I b) := Fintype.ofFinite _
  let br : D := ⟨componentVertex C b, b, Or.inl rfl, rfl⟩
  have hI := casebi_terminal_interior_two G A B x (componentVertex C yr) s k hmax hBs hk
    htri hquad hd hno C yr rfl I b hT hyI
  have hD : TwoConnected (G.induce D) := twoConnected_of_graphIso
    (C.toSimpleGraph.induce (fragmentBlock I b)) (G.induce D)
    (componentRegionGraphIso C (fragmentBlock I b))
    (terminalFragment_twoConnected C.toSimpleGraph I b hT hI)
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  have hDA : Disjoint D A := Set.disjoint_left.mpr
    (fun _ hzD hzA => Set.disjoint_left.mp hDQ hzD (Or.inl hzA))
  have hDS : Disjoint D S := cliqueBlock_boundary_disjoint G D A x (componentVertex C b) hDA
  let : Fintype {w : (D ∪ S : Set V) // w.1 ∉ S} := Fintype.ofFinite _
  let : Fintype (IdentificationVertex {w : (D ∪ S : Set V) | w.1 ∈ S}) := regionIdentificationFintype D S
  have hroot := cliqueBlock_quotient_rooted G D A x hDA br hD hS
  have hsk := casebi_counterexample_part_lt_k G A B x (componentVertex C yr) s k hmax.1 hBs hG hno
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hdeg : NonrootDegreeAtLeast (regionIdentificationGraph G D S) none
      (some (regionRetainedVertex D S hDS br)) (m + 1) := by
    intro z hzn hzb
    cases z with
    | none => exact False.elim (hzn rfl)
    | some a =>
      have haD : a.1.1 ∈ D := a.1.2.elim id (fun h => False.elim (a.2 h))
      let v : D := ⟨a.1.1, haD⟩
      have hvb : v.1 ≠ componentVertex C b := fun he =>
        hzb (congrArg Option.some (Subtype.ext (Subtype.ext he)))
      have hrep : a = regionRetainedVertex D S hDS v := Subtype.ext (Subtype.ext rfl)
      change k - s + 1 ≤ ((regionIdentificationGraph G D S).neighborSet (some a)).ncard
      rw [hrep]
      exact casebi_first_part_quotient_degree G A B x (componentVertex C yr) s k hmax hBs
        (by omega) htri hquad hd C yr rfl I b hT hyI v hvb
  have hltNat : Nat.card (IdentificationVertex {w : (D ∪ S : Set V) | w.1 ∈ S}) < Nat.card V := by
    rw [regionIdentification_card D S hDS]
    have hbound := Set.ncard_le_card (D ∪ (A ∪ B))
    rw [Set.ncard_union_eq hDQ] at hbound
    have hQcard : 2 ≤ (A ∪ B).ncard := hmax.1.2.2.2.2.1.trans
      (Set.ncard_le_ncard (show B ⊆ A ∪ B from Set.subset_union_right))
    omega
  have hlt : Fintype.card (IdentificationVertex {w : (D ∪ S : Set V) | w.1 ∈ S}) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hltNat
  obtain ⟨a, d, P, hP⟩ := ih (IdentificationVertex {w : (D ∪ S : Set V) | w.1 ∈ S})
    (regionIdentificationGraph G D S) none (some (regionRetainedVertex D S hDS br))
    m hlt hm hroot hdeg
  obtain ⟨starts, lifts, hs, hfam, _hlen, hsupp⟩ := identification_induced_family_lift
    G (D ∪ S) S (regionRetainedVertex D S hDS br) m a d P hP
  change (∀ i : Fin m, G.Walk (starts i) (componentVertex C b)) at lifts
  obtain ⟨R, hR, hRQ, hRD⟩ := terminal_component_original_tail C I b yr hT hyI
  have hmeetR : ∀ i z, z ∈ (lifts i).support → z ∈ R.support → z = componentVertex C b := by
    intro i z hz hzR
    rcases (hsupp i z hz).1 with hzD | hzS
    · exact hRD z hzR hzD
    · exact False.elim (hRQ z hzR (Or.inl hzS.1))
  let L : ∀ i : Fin m, G.Walk (componentVertex C yr) (starts i) :=
    fun i => ((lifts i).append R).reverse
  have hL : ∀ i, (L i).IsPath := fun i =>
    (append_isPath_of_only_common_endpoint (hfam.2.2 i).1 hR (hmeetR i)).reverse
  have hLl : ∀ i, (L i).length = a + R.length + i.val * d := by
    intro i
    change ((lifts i).append R).reverse.length = a + R.length + i.val * d
    rw [Walk.length_reverse, Walk.length_append]
    have hlen : (lifts i).length = a + i.val * d := (hfam.2.2 i).2
    omega
  have hprefix : ∀ i : Fin m, ∃ F : Fin (s + 1) → G.Walk x (starts i),
      ∀ j, (F j).IsPath ∧ (F j).length = 1 + j.val * 2 ∧
        ∀ z ∈ (F j).support, z ∈ A ∪ B := by
    intro i
    exact casebi_set_odd_prefix G A B (s + 1) x (starts i) hmax.1.1 hmax.1.2.1
      hmax.1.2.2.1 (hs i).1 (by have hh := hmax.1.2.2.2.2.2; omega) (by omega)
  choose F hF using hprefix
  let Q : ∀ i : Fin m, Fin (s + 1) → G.Walk (starts i) x := fun i j => (F i j).reverse
  have hQ : ∀ i j, (Q i j).IsPath := fun i j => (hF i j).1.reverse
  have hQl : ∀ i j, (Q i j).length = 1 + j.val * 2 := by
    intro i j
    change (F i j).reverse.length = 1 + j.val * 2
    rw [Walk.length_reverse]
    exact (hF i j).2.1
  have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (Q i j).support → z = starts i := by
    intro i j z hzL hzQ
    have hzF : z ∈ (F i j).support := by simpa only [Q, Walk.support_reverse, List.mem_reverse] using hzQ
    have hzCore := (hF i j).2.2 z hzF
    have hzA : z ∈ ((lifts i).append R).support := by
      simpa only [L, Walk.support_reverse, List.mem_reverse] using hzL
    rw [Walk.support_append] at hzA
    rcases List.mem_append.mp hzA with hzLift | hzR
    · have hh := hsupp i z hzLift
      rcases hh.1 with hzD | hzS
      · exact False.elim (Set.disjoint_left.mp hDQ hzD hzCore)
      · exact hh.2.elim id (fun hn => False.elim (hn hzS))
    · exact False.elim (hRQ z (List.mem_of_mem_tail hzR) hzCore)
  have hyx := admissible_path_concatenation (G := G) hm (by omega : 1 ≤ s + 1)
    (by have ha := hfam.1; omega : 2 ≤ a + R.length) (by omega : 1 ≤ (1 : ℕ))
    hfam.2.1 (Or.inr rfl) starts L Q hL hQ hLl hQl hmeet
  have hcount : m + (s + 1) - 1 = k := by dsimp [m]; omega
  rw [hcount] at hyx
  obtain ⟨a0, d0, F0, hF0⟩ := hyx
  exact ⟨a0, d0, (fun i => (F0 i).reverse),
    (admissible_family_reverse G (componentVertex C yr) x k a0 d0 F0 hF0).1⟩

theorem casebi_feasible_no_first_part [Fintype V] (G : SimpleGraph V)
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
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hyI : yr ∉ I) : ∀ v ∈ I, ∀ a ∈ A, ¬G.Adj (componentVertex C v) a := by
  intro v hvI a haA eva
  have hax : a ≠ x := fun he => Set.disjoint_left.mp hmax.1.1 haA
    (Eq.mpr (congrArg (fun a : V => a ∈ B) he) hmax.1.2.2.1)
  have hvb : componentVertex C v ≠ componentVertex C b := fun he =>
    hT.2.1 (Eq.mp (congrArg (fun v : C.supp => v ∈ I) (componentVertex_injective C he)) hvI)
  have hS : (cliqueBlockBoundary G (componentRegion C (fragmentBlock I b)) A x
      (componentVertex C b)).Nonempty :=
    ⟨a, haA, hax, componentVertex C v, ⟨v, Or.inr hvI, rfl⟩, hvb, eva⟩
  exact hno (casebi_feasible_first_part_family G A B x y s k hmax hBs hk hG htri hquad
    hd hno ih C yr hY I b hT hyI hS)

#print axioms casebi_first_part_quotient_degree
#print axioms casebi_feasible_first_part_family
#print axioms casebi_feasible_no_first_part
end TaskH.Gao
