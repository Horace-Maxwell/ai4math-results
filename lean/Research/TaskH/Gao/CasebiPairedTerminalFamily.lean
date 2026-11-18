import Research.TaskH.Gao.CasebiNonsingletonCaseOne

/-! Both retained second-side roots have actual k-1 families in their terminal regions. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_paired_terminal_retained_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y r o : V) (k : ℕ) (hx : x ∈ B) (hB : B = {r, o})
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) (yr : C.supp)
    (hY : componentVertex C yr = y) (I : Set C.supp) (b : C.supp)
    (hT : TerminalFragment C.toSimpleGraph I b) (hyI : yr ∉ I)
    (hnoA : ∀ w ∈ I, ∀ z ∈ A, ¬G.Adj (componentVertex C w) z)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (realRootGraph G (componentRegion C (fragmentBlock I b)) r)
      (realRootPoint (componentRegion C (fragmentBlock I b)) r)
      (realRootBlockPoint (componentRegion C (fragmentBlock I b)) r
        ⟨componentVertex C b, b, Or.inl rfl, rfl⟩) k := by
  classical
  let D := componentRegion C (fragmentBlock I b)
  let S := D ∪ {r}
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  intro v hvr hvb
  have hvD : v.1 ∈ D := v.2.elim id (fun he => False.elim (hvr (Subtype.ext he)))
  have hvb' : v.1 ≠ componentVertex C b := fun he => hvb (Subtype.ext he)
  have hvx : v.1 ≠ x := fun he => Set.disjoint_left.mp hDQ hvD
    (Eq.mpr (congrArg (fun v : V => v ∈ A ∪ B) he) (Or.inr hx))
  have hBy : y ∈ D → y = componentVertex C b := by
    rw [← hY]; exact component_fragment_y_boundary C I b yr hyI
  have hvy : v.1 ≠ y := fun he => hvb'
    (he.trans (hBy (Eq.mp (congrArg (fun v : V => v ∈ D) he) hvD)))
  obtain ⟨w, hwI, he⟩ := casebi_fragment_nonroot_interior G (A ∪ B) C I b ⟨v.1, hvD⟩ hvb'
  have hsub : G.neighborSet v.1 \ S ⊆ {o} := by
    rintro z ⟨evz, hzS⟩
    rcases component_fragment_original_cover C I b hT v.1 hvD hvb' z evz with hzD | hzA | hzB
    · exact False.elim (hzS (Or.inl hzD))
    · exact False.elim (hnoA w hwI z hzA
        (Eq.mpr (congrArg (fun v : V => G.Adj v z) he) evz))
    · rw [hB] at hzB
      rcases hzB with hzr | hzo
      · exact False.elim (hzS (Or.inr hzr))
      · exact hzo
  have hsmall : (G.neighborSet v.1 \ S).ncard ≤ 1 := by
    simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub
  have heq : ((realRootGraph G D r).neighborSet v).ncard = (G.neighborSet v.1 ∩ S).ncard := by
    apply Set.ncard_congr (fun z _ => z.1)
    · intro z hz; exact ⟨hz, z.2⟩
    · intro z w _ _ he; exact Subtype.ext he
    · rintro z ⟨evz, hzS⟩; exact ⟨⟨z, hzS⟩, evz, rfl⟩
  have hp := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet v.1) S
  have ho := hd v.1 hvx hvy
  rw [heq]
  omega

theorem casebi_actual_terminal_child_family [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y r o : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (n : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ n → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (n + 1) → HasAdmissiblePaths J a d n)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hyI : yr ∉ I) (hr : r ∈ B) (hB : B = {r, o}) :
    ∃ a d : ℕ, ∃ P : Fin (k - 1) → G.Walk r (componentVertex C b),
      AdmissiblePathFamily G r (componentVertex C b) (k - 1) a d P ∧
      ∀ i z, z ∈ (P i).support → z ∈ componentRegion C (fragmentBlock I b) ∨ z = r := by
  classical
  let D := componentRegion C (fragmentBlock I b)
  let m := k - 1
  let : Fintype D := Fintype.ofFinite _
  let : Fintype (fragmentBlock I b) := Fintype.ofFinite _
  let : Fintype (D ∪ {r} : Set V) := Fintype.ofFinite _
  let br : D := ⟨componentVertex C b, b, Or.inl rfl, rfl⟩
  have hI := casebi_terminal_interior_two G A B x y s k hmax hBs hk
    htri hquad hd hno C yr hY I b hT hyI
  have hD : TwoConnected (G.induce D) := twoConnected_of_graphIso
    (C.toSimpleGraph.induce (fragmentBlock I b)) (G.induce D)
    (componentRegionGraphIso C (fragmentBlock I b))
    (terminalFragment_twoConnected C.toSimpleGraph I b hT hI)
  have hnoA := casebi_feasible_no_first_part G A B x y s k hmax hBs hk
    hG htri hquad hd hno ih C yr hY I b hT hyI
  have hrigid := casebi_feasible_second_side_rigidity G A B x y s k hmax hBs hk
    hG htri hquad hd hno ih C yr hY I b hT hyI
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  have hrD : r ∉ D := fun h => Set.disjoint_left.mp hDQ h (Or.inr hr)
  obtain ⟨w, hwI, ewr⟩ := hrigid.2 r hr
  let wr : D := ⟨componentVertex C w, w, Or.inr hwI, rfl⟩
  have hwb : wr ≠ br := by
    intro he
    have hwbNative : componentVertex C w = componentVertex C b :=
      congrArg (fun z : D => z.1) he
    have hwb' : w = b := componentVertex_injective C hwbNative
    exact hT.2.1 (Eq.mp (congrArg (fun z : C.supp => z ∈ I) hwb') hwI)
  have hroot := realRoot_rooted_from_actual_spoke G D r hrD br wr hD ewr.symm hwb
  have hdeg := casebi_paired_terminal_retained_degree G A B x y r o k hmax.1.2.2.1 hB
    C yr hY I b hT hyI hnoA hd
  have hltNat : Nat.card (D ∪ {r} : Set V) < Nat.card V := by
    rw [Nat.card_coe_set_eq, Set.union_singleton, Set.ncard_insert_of_notMem hrD]
    have hn := Set.ncard_le_card (D ∪ (A ∪ B))
    rw [Set.ncard_union_eq hDQ] at hn
    have hQ2 : 2 ≤ (A ∪ B).ncard := hmax.1.2.2.2.2.1.trans
      (Set.ncard_le_ncard (show B ⊆ A ∪ B from Set.subset_union_right))
    omega
  have hlt : Fintype.card (D ∪ {r} : Set V) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hltNat
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmk : m + 1 = k := by dsimp [m]; omega
  have hdeg' : NonrootDegreeAtLeast (realRootGraph G D r) (realRootPoint D r)
      (realRootBlockPoint D r br) (m + 1) := by rw [hmk]; exact hdeg
  obtain ⟨a, d, p, hp⟩ := ih (D ∪ {r} : Set V) (realRootGraph G D r)
    (realRootPoint D r) (realRootBlockPoint D r br) m hlt hm hroot hdeg'
  let f : realRootGraph G D r →g G := (Embedding.induce (D ∪ {r} : Set V)).toHom
  have hmapped := admissible_family_map (realRootGraph G D r) G f Subtype.val_injective
    (realRootPoint D r) (realRootBlockPoint D r br) m a d p hp
  refine ⟨a, d, (fun i => (p i).map f), hmapped.1, ?_⟩
  intro i z hz
  obtain ⟨v, _hv, he⟩ := (hmapped.2 i z).mp hz
  have he' : v.1 = z := he
  rcases v.2 with hv | hv
  · exact Or.inl (Eq.mp (congrArg (fun z : V => z ∈ D) he') hv)
  · exact Or.inr (he'.symm.trans hv)

#print axioms casebi_paired_terminal_retained_degree
#print axioms casebi_actual_terminal_child_family
end TaskH.Gao
