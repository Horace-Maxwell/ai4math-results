import Research.TaskH.Gao.CasebiFeasibleSecondDegree

/-! The actual feasible block forces s=1 and both original Q2 attachments. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_feasible_second_part_family [Fintype V] (G : SimpleGraph V)
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
    (hcase : 2 ≤ s ∨ ∀ w ∈ I, ¬G.Adj (componentVertex C w) x)
    (hS : (cliqueBlockBoundary G (componentRegion C (fragmentBlock I b)) B x
      (componentVertex C b)).Nonempty) : HasAdmissiblePaths G x y k := by
  subst y
  classical
  let D := componentRegion C (fragmentBlock I b)
  let S := cliqueBlockBoundary G D B x (componentVertex C b)
  let m := k - s + 1
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
  have hDB : Disjoint D B := Set.disjoint_left.mpr
    (fun _ hzD hzB => Set.disjoint_left.mp hDQ hzD (Or.inr hzB))
  have hDS : Disjoint D S := cliqueBlock_boundary_disjoint G D B x (componentVertex C b) hDB
  let : Fintype {w : (D ∪ S : Set V) // w.1 ∉ S} := Fintype.ofFinite _
  let : Fintype (IdentificationVertex {w : (D ∪ S : Set V) | w.1 ∈ S}) := regionIdentificationFintype D S
  have hroot := cliqueBlock_quotient_rooted G D B x hDB br hD hS
  have hsk := casebi_counterexample_part_lt_k G A B x (componentVertex C yr) s k hmax.1 hBs hG hno
  have hspos : 1 ≤ s := by have hh := hmax.1.2.2.2.2.1; omega
  have hnoA := casebi_feasible_no_first_part G A B x (componentVertex C yr) s k hmax hBs hk
    hG htri hquad hd hno ih C yr rfl I b hT hyI
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
      change k - s + 2 ≤ ((regionIdentificationGraph G D S).neighborSet (some a)).ncard
      rw [hrep]
      exact casebi_second_part_quotient_degree G A B x (componentVertex C yr) s k hmax hBs
        hspos (by omega) hd C yr rfl I b hT hyI hnoA hcase v hvb
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
    · exact False.elim (hRQ z hzR (Or.inr hzS.1))
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
  have hprefix : ∀ i : Fin m, ∃ F : Fin s → G.Walk x (starts i),
      ∀ j, (F j).IsPath ∧ (F j).length = 2 + j.val * 2 ∧
        ∀ z ∈ (F j).support, z ∈ A ∪ B := by
    intro i
    exact casebi_set_even_prefix G A B s x (starts i) hmax.1.1 hmax.1.2.1
      hmax.1.2.2.1 (hs i).1 (hs i).2.1.symm
      (by have hh := hmax.1.2.2.2.2.2; omega) (by omega)
  choose F hF using hprefix
  let Q : ∀ i : Fin m, Fin s → G.Walk (starts i) x := fun i j => (F i j).reverse
  have hQ : ∀ i j, (Q i j).IsPath := fun i j => (hF i j).1.reverse
  have hQl : ∀ i j, (Q i j).length = 2 + j.val * 2 := by
    intro i j
    change (F i j).reverse.length = 2 + j.val * 2
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
  have hyx := admissible_path_concatenation (G := G) hm hspos
    (by have ha := hfam.1; omega : 2 ≤ a + R.length) (by omega : 1 ≤ (2 : ℕ))
    hfam.2.1 (Or.inr rfl) starts L Q hL hQ hLl hQl hmeet
  have hcount : m + s - 1 = k := by dsimp [m]; omega
  rw [hcount] at hyx
  obtain ⟨a0, d0, F0, hF0⟩ := hyx
  exact ⟨a0, d0, (fun i => (F0 i).reverse),
    (admissible_family_reverse G (componentVertex C yr) x k a0 d0 F0 hF0).1⟩

theorem casebi_feasible_second_side_rigidity [Fintype V] (G : SimpleGraph V)
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
    (hyI : yr ∉ I) : s = 1 ∧ ∀ z ∈ B, ∃ w ∈ I, G.Adj (componentVertex C w) z := by
  classical
  let D := componentRegion C (fragmentBlock I b)
  let S := cliqueBlockBoundary G D B x (componentVertex C b)
  have hS : S.Nonempty := by
    by_contra hn
    have hem : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    exact hno (casebi_empty_second_boundary_family G A B x y s k hmax hBs hk hG htri hquad
      hd hno ih C yr hY I b hT hyI hem)
  have hncase : ¬(2 ≤ s ∨ ∀ w ∈ I, ¬G.Adj (componentVertex C w) x) := by
    intro hc
    exact hno (casebi_feasible_second_part_family G A B x y s k hmax hBs hk hG htri hquad
      hd hno ih C yr hY I b hT hyI hc hS)
  have hs1 : s = 1 := by
    have hspos : 1 ≤ s := by have hh := hmax.1.2.2.2.2.1; omega
    have hn2 : ¬2 ≤ s := fun h => hncase (Or.inl h)
    omega
  have hxAttach : ∃ w ∈ I, G.Adj (componentVertex C w) x := by
    by_contra hn
    apply hncase
    right
    intro w hw exw
    exact hn ⟨w, hw, exw⟩
  obtain ⟨z, hzS⟩ := hS
  obtain ⟨v, hvD, hvb, evz⟩ := hzS.2.2
  obtain ⟨w, hwI, he⟩ := casebi_fragment_nonroot_interior G (A ∪ B) C I b ⟨v, hvD⟩ hvb
  have hwz : G.Adj (componentVertex C w) z :=
    Eq.mpr (congrArg (fun v : V => G.Adj v z) he) evz
  have hpairSub : ({x, z} : Set V) ⊆ B := by
    rintro t (htx | htz)
    · exact Eq.mpr (congrArg (fun v : V => v ∈ B) htx) hmax.1.2.2.1
    · exact Eq.mpr (congrArg (fun v : V => v ∈ B) htz) hzS.1
  have hBeq : B = ({x, z} : Set V) := by
    symm
    apply Set.eq_of_subset_of_ncard_le hpairSub
    rw [Set.ncard_pair hzS.2.1.symm]
    omega
  refine ⟨hs1, ?_⟩
  intro t ht
  rw [hBeq] at ht
  rcases ht with htx | htz
  · obtain ⟨a, ha, eax⟩ := hxAttach
    exact ⟨a, ha, Eq.mpr (congrArg (fun t : V => G.Adj (componentVertex C a) t) htx) eax⟩
  · exact ⟨w, hwI, Eq.mpr (congrArg (fun t : V => G.Adj (componentVertex C w) t) htz) hwz⟩

#print axioms casebi_feasible_second_part_family
#print axioms casebi_feasible_second_side_rigidity
end TaskH.Gao
