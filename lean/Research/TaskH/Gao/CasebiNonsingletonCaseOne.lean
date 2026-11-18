import Research.TaskH.Gao.CasebiOutsideComponent
import Research.TaskH.Gao.RealRootComponentAndLift
import Research.TaskH.Gao.Base

/-! Original nonsingleton Case1: two actual strict children and complete original AP contradiction. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_walk_stays_component (G : SimpleGraph V) (Q : Set V)
    (C : (G.induce Qᶜ).ConnectedComponent) :
    ∀ {v z : V} (P : G.Walk v z), v ∈ componentRegion C Set.univ →
      (∀ w ∈ P.support, w ∉ Q) → ∀ w ∈ P.support, w ∈ componentRegion C Set.univ := by
  intro v z P
  induction P with
  | @nil v =>
    intro hv _hAvoid w hw
    have he : w = v := by simpa only [Walk.support_nil, List.mem_singleton] using hw
    exact Eq.mpr (congrArg (fun w : V => w ∈ componentRegion C Set.univ) he) hv
  | @cons v w z e P ih =>
    intro hv hAvoid t ht
    have hwQ : w ∉ Q := hAvoid w (by
      rw [Walk.support_cons]; exact List.mem_cons_of_mem v (Walk.start_mem_support P))
    have hvC := hv
    obtain ⟨vr, _hvr, he⟩ := hv
    have evw : (G.induce Qᶜ).Adj vr.1 ⟨w, hwQ⟩ :=
      Eq.mpr (congrArg (fun v : V => G.Adj v w) he) e
    let wr : C.supp := ⟨⟨w, hwQ⟩, C.mem_supp_of_adj_mem_supp vr.2 evw⟩
    have hwC : w ∈ componentRegion C Set.univ := ⟨wr, Set.mem_univ wr, rfl⟩
    have hAvoidP : ∀ a ∈ P.support, a ∉ Q := fun a ha =>
      hAvoid a (by rw [Walk.support_cons]; exact List.mem_cons_of_mem v ha)
    rw [Walk.support_cons] at ht
    rcases List.mem_cons.mp ht with he | ht
    · exact Eq.mpr (congrArg (fun t : V => t ∈ componentRegion C Set.univ) he) hvC
    · exact ih hwC hAvoidP t ht

theorem casebi_real_second_block_degree [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y a : V) (k : ℕ) (hx : x ∈ B) (_ha : a ∈ B) (hB : B = {x, a})
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) (yr : C.supp)
    (hY : componentVertex C yr = y) (I : Set C.supp) (b : C.supp)
    (hT : TerminalFragment C.toSimpleGraph I b) (hyI : yr ∉ I)
    (hnoA : ∀ w ∈ I, ∀ z ∈ A, ¬G.Adj (componentVertex C w) z)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) :
    NonrootDegreeAtLeast (realRootGraph G (componentRegion C (fragmentBlock I b)) a)
      (realRootPoint (componentRegion C (fragmentBlock I b)) a)
      (realRootBlockPoint (componentRegion C (fragmentBlock I b)) a
        ⟨componentVertex C b, b, Or.inl rfl, rfl⟩) k := by
  classical
  let D := componentRegion C (fragmentBlock I b)
  let S := D ∪ {a}
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  intro v hva hvb
  have hvD : v.1 ∈ D := v.2.elim id (fun he => False.elim (hva (Subtype.ext he)))
  have hvb' : v.1 ≠ componentVertex C b := fun he => hvb (Subtype.ext he)
  have hvx : v.1 ≠ x := fun he => Set.disjoint_left.mp hDQ hvD
    (Eq.mpr (congrArg (fun v : V => v ∈ A ∪ B) he) (Or.inr hx))
  have hBy : y ∈ D → y = componentVertex C b := by
    rw [← hY]; exact component_fragment_y_boundary C I b yr hyI
  have hvy : v.1 ≠ y := fun he => hvb'
    (he.trans (hBy (Eq.mp (congrArg (fun v : V => v ∈ D) he) hvD)))
  obtain ⟨w, hwI, he⟩ := casebi_fragment_nonroot_interior G (A ∪ B) C I b ⟨v.1, hvD⟩ hvb'
  have hsub : G.neighborSet v.1 \ S ⊆ {x} := by
    rintro z ⟨evz, hzS⟩
    rcases component_fragment_original_cover C I b hT v.1 hvD hvb' z evz with hzD | hzA | hzB
    · exact False.elim (hzS (Or.inl hzD))
    · exact False.elim (hnoA w hwI z hzA
        (Eq.mpr (congrArg (fun v : V => G.Adj v z) he) evz))
    · rw [hB] at hzB
      rcases hzB with hzx | hza
      · exact hzx
      · exact False.elim (hzS (Or.inr hza))
  have hsmall : (G.neighborSet v.1 \ S).ncard ≤ 1 := by
    simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub
  have heq : ((realRootGraph G D a).neighborSet v).ncard = (G.neighborSet v.1 ∩ S).ncard := by
    apply Set.ncard_congr (fun z _ => z.1)
    · intro z hz; exact ⟨hz, z.2⟩
    · intro z w _ _ he; exact Subtype.ext he
    · rintro z ⟨evz, hzS⟩; exact ⟨⟨z, hzS⟩, evz, rfl⟩
  have hp := Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet v.1) S
  have ho := hd v.1 hvx hvy
  rw [heq]
  omega

theorem casebi_nonsingleton_case_one_contradiction [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (r : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ r → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (r + 1) → HasAdmissiblePaths J a d r)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y) (hC : 2 ≤ Fintype.card C.supp)
    (hcase : ∀ w : C.supp, w ≠ yr → ∀ z ∈ A, ¬G.Adj (componentVertex C w) z) : False := by
  subst y
  classical
  obtain ⟨I, b, hT, hyI, hI, ⟨iD, hD⟩, R, hR, hRQ, hRD⟩ :=
    casebi_actual_feasible_block_exists G A B x (componentVertex C yr) s k hmax hBs hk
      htri hquad hd hno C yr rfl hC
  have hrigid := casebi_feasible_second_side_rigidity G A B x (componentVertex C yr) s k hmax hBs hk
    hG htri hquad hd hno ih C yr rfl I b hT hyI
  have hnoA := casebi_feasible_no_first_part G A B x (componentVertex C yr) s k hmax hBs hk
    hG htri hquad hd hno ih C yr rfl I b hT hyI
  have hxB : x ∈ B := hmax.1.2.2.1
  obtain ⟨a, haB, hax⟩ := Set.exists_ne_of_one_lt_ncard
    (by have hh := hmax.1.2.2.2.2.1; omega : 1 < B.ncard) x
  have hBeq : B = ({x, a} : Set V) := by
    symm
    apply Set.eq_of_subset_of_ncard_le (show ({x, a} : Set V) ⊆ B from by
      rintro z (hzx | hza)
      · exact Eq.mpr (congrArg (fun z : V => z ∈ B) hzx) hxB
      · exact Eq.mpr (congrArg (fun z : V => z ∈ B) hza) haB)
    rw [Set.ncard_pair hax.symm]
    have hs1 := hrigid.1
    omega
  let D := componentRegion C (fragmentBlock I b)
  let E := componentRegion C Set.univ
  let S := Eᶜ
  let m := k - 1
  let : Fintype D := iD
  let : Fintype S := Fintype.ofFinite _
  let : Fintype (D ∪ {a} : Set V) := Fintype.ofFinite _
  let br : D := ⟨componentVertex C b, b, Or.inl rfl, rfl⟩
  have hxS : x ∈ S := casebi_core_outside_component G (A ∪ B) C x (Or.inr hxB)
  have haS : a ∈ S := casebi_core_outside_component G (A ∪ B) C a (Or.inr haB)
  let xr : S := ⟨x, hxS⟩
  let ar : S := ⟨a, haS⟩
  have hAne : A.Nonempty := (Set.ncard_pos (Set.toFinite A)).mp
    (by have hh := hmax.1.2.2.2.2.1; have hBA := hmax.1.2.2.2.2.2; omega)
  have hrootOut := casebi_outside_component_rooted G A B x a hmax.1.1 hmax.1.2.1 hBeq
    hax.symm hAne hG C
  have hdegOut := casebi_outside_component_degree G A B x (componentVertex C yr) a k hBeq C yr rfl
    hcase hd hxS haS
  have hyE : componentVertex C yr ∈ E := ⟨yr, Set.mem_univ yr, rfl⟩
  have hltOutNat : Nat.card S < Nat.card V := by
    have hdis : Disjoint S ({componentVertex C yr} : Set V) := Set.disjoint_left.mpr
      (fun _ hzS hzY => hzS (Eq.mpr (congrArg (fun z : V => z ∈ E) hzY) hyE))
    have hn := Set.ncard_le_card (S ∪ {componentVertex C yr})
    rw [Set.ncard_union_eq hdis, Set.ncard_singleton] at hn
    rw [Nat.card_coe_set_eq]
    omega
  have hltOut : Fintype.card S < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hltOutNat
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmk : m + 1 = k := by dsimp [m]; omega
  have hdegOut' : NonrootDegreeAtLeast (G.induce S) xr ar (m + 1) := by rw [hmk]; exact hdegOut
  obtain ⟨ao, dout, O, hO⟩ := ih S (G.induce S) xr ar m hltOut hm hrootOut hdegOut'
  let fo : G.induce S →g G := (Embedding.induce S).toHom
  have hmapO := admissible_family_map (G.induce S) G fo Subtype.val_injective xr ar m ao dout O hO
  let P : Fin m → G.Walk x a := fun i => (O i).map fo
  have hPS : ∀ i z, z ∈ (P i).support → z ∈ S := by
    intro i z hz
    obtain ⟨v, _hv, he⟩ := (hmapO.2 i z).mp hz
    have he' : v.1 = z := he
    exact Eq.mp (congrArg (fun z : V => z ∈ S) he') v.2
  have hDQ : Disjoint D (A ∪ B) := componentRegion_disjoint C (fragmentBlock I b)
  have haD : a ∉ D := fun haD => Set.disjoint_left.mp hDQ haD (Or.inr haB)
  obtain ⟨w, hwI, ewa⟩ := hrigid.2 a haB
  let wr : D := ⟨componentVertex C w, w, Or.inr hwI, rfl⟩
  have hwb : wr ≠ br := by
    intro he
    have he' : componentVertex C w = componentVertex C b :=
      congrArg (fun q : D => q.1) he
    have hwb' : w = b := componentVertex_injective C he'
    exact hT.2.1 (Eq.mp (congrArg (fun v : C.supp => v ∈ I) hwb') hwI)
  have hrootD := realRoot_rooted_from_actual_spoke G D a haD br wr hD ewa.symm hwb
  have hdegD := casebi_real_second_block_degree G A B x (componentVertex C yr) a k hxB haB hBeq C yr
    rfl I b hT hyI hnoA hd
  have hdegD' : NonrootDegreeAtLeast (realRootGraph G D a) (realRootPoint D a)
      (realRootBlockPoint D a br) (m + 1) := by rw [hmk]; exact hdegD
  have hltDNat : Nat.card (D ∪ {a} : Set V) < Nat.card V := by
    rw [Nat.card_coe_set_eq, Set.union_singleton, Set.ncard_insert_of_notMem haD]
    have hn := Set.ncard_le_card (D ∪ (A ∪ B))
    rw [Set.ncard_union_eq hDQ] at hn
    have hQ2 : 2 ≤ (A ∪ B).ncard := hmax.1.2.2.2.2.1.trans
      (Set.ncard_le_ncard (show B ⊆ A ∪ B from Set.subset_union_right))
    omega
  have hltD : Fintype.card (D ∪ {a} : Set V) < Fintype.card V := by
    simpa only [Fintype.card_eq_nat_card] using hltDNat
  obtain ⟨ai, di, N, hN⟩ := ih (D ∪ {a} : Set V) (realRootGraph G D a) (realRootPoint D a)
    (realRootBlockPoint D a br) m hltD hm hrootD hdegD'
  let fi : realRootGraph G D a →g G := (Embedding.induce (D ∪ {a} : Set V)).toHom
  have hmapN := admissible_family_map (realRootGraph G D a) G fi Subtype.val_injective
    (realRootPoint D a) (realRootBlockPoint D a br) m ai di N hN
  let Q : Fin m → G.Walk a (componentVertex C b) := fun i => (N i).map fi
  have hQR : ∀ i z, z ∈ (Q i).support → z ∈ R.support → z = componentVertex C b := by
    intro i z hz hzR
    obtain ⟨v, _hv, he⟩ := (hmapN.2 i z).mp hz
    have he' : v.1 = z := he
    rcases v.2 with hvD | hva
    · exact hRD z hzR (Eq.mp (congrArg (fun z : V => z ∈ D) he') hvD)
    · have hza : z = a := he'.symm.trans hva
      exact False.elim (hRQ z hzR (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ B) hza) haB)))
  let L : Fin m → G.Walk a (componentVertex C yr) := fun i => (Q i).append R
  have hL : ∀ i, (L i).IsPath := fun i =>
    append_isPath_of_only_common_endpoint (hmapN.1.2.2 i).1 hR (hQR i)
  have hLl : ∀ i, (L i).length = ai + R.length + i.val * di := by
    intro i
    change ((Q i).append R).length = ai + R.length + i.val * di
    rw [Walk.length_append]
    have hh : (Q i).length = ai + i.val * di := (hmapN.1.2.2 i).2
    omega
  have hRE : ∀ z ∈ R.support, z ∈ E := casebi_walk_stays_component G (A ∪ B) C R
    ⟨b, Set.mem_univ b, rfl⟩ hRQ
  have hLE : ∀ i z, z ∈ (L i).support → z ∈ E ∨ z = a := by
    intro i z hz
    change z ∈ ((Q i).append R).support at hz
    rw [Walk.support_append] at hz
    rcases List.mem_append.mp hz with hzQ | hzR
    · obtain ⟨v, _hv, he⟩ := (hmapN.2 i z).mp hzQ
      have he' : v.1 = z := he
      rcases v.2 with hvD | hva
      · obtain ⟨w, _hw, hwv⟩ := hvD
        exact Or.inl ⟨w, Set.mem_univ w, hwv.trans he'⟩
      · exact Or.inr (he'.symm.trans hva)
    · exact Or.inl (hRE z (List.mem_of_mem_tail hzR))
  have hmeet : ∀ i j z, z ∈ (P i).support → z ∈ (L j).support → z = a := by
    intro i j z hzP hzL
    rcases hLE j z hzL with hzE | he
    · exact False.elim (hPS i z hzP hzE)
    · exact he
  have hfamily := admissible_path_concatenation (G := G) hm hm hO.1
    (by have hh := hN.1; omega : 1 ≤ ai + R.length) hO.2.1 hN.2.1
    (fun _ => a) P (fun _ j => L j) (fun i => (hmapO.1.2.2 i).1)
    (fun _ j => hL j) (fun i => (hmapO.1.2.2 i).2) (fun _ j => hLl j) hmeet
  exact hno (has_admissible_initial_segment (by dsimp [m]; omega : k ≤ m + m - 1) hfamily)

#print axioms casebi_walk_stays_component
#print axioms casebi_real_second_block_degree
#print axioms casebi_nonsingleton_case_one_contradiction
end TaskH.Gao
