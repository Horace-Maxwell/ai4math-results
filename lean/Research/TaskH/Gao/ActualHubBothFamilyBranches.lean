import Research.TaskH.Gao.ActualHubSideConnectors
import Research.TaskH.Gao.QualifiedHubActualChild
import Research.TaskH.Gao.CasebiHubActualShortFamily
import Research.TaskH.Gao.CasebiPairedTerminalFamily

/-! Both original k-family contradictions for an ACTUAL maximal-region hub
with explicit actual component-side membership. This is NOT an assertion
that the missing incidence-route qualification has been proved. No paths,
child degree/order or desired family is an input of this local theorem. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem actual_maximal_hub_sides_original_contradiction [Fintype V]
    (G : SimpleGraph V) (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (hG : TwoConnected G) (htri : CasebiNoRootTriangle G x y)
    (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1))
    (ih : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (a d : W) (n : ℕ),
      Fintype.card W < Fintype.card V → 1 ≤ n → RootedTwoConnected J a d →
      NonrootDegreeAtLeast J a d (n + 1) → HasAdmissiblePaths J a d n)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (S : Set C.supp) [Fintype S] (u v : S) (huv : u ≠ v)
    (hS : TwoConnected (C.toSimpleGraph.induce S))
    (hmaxS : ∀ (T : Set C.supp) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (C.toSimpleGraph.induce T) → T ⊆ S)
    (hcut : ∀ z ∈ S, ¬(C.toSimpleGraph.induce {w | w ≠ z}).Connected →
      z = u.1 ∨ z = v.1)
    (hyS : yr ∈ S → yr = v.1)
    (I : Set C.supp) (b : C.supp) (hI : TerminalFragment C.toSimpleGraph I b)
    (E : (C.toSimpleGraph.induce Sᶜ).ConnectedComponent)
    (hEu : carrierAttachment C.toSimpleGraph S
      (maximal_twoConnected_region_single_attachment C.toSimpleGraph S C.connected_toSimpleGraph hS hmaxS) E = u)
    (hIE : I ⊆ componentRegion E Set.univ)
    (hySide : yr = v.1 ∨ ∃ F : (C.toSimpleGraph.induce Sᶜ).ConnectedComponent,
      carrierAttachment C.toSimpleGraph S
        (maximal_twoConnected_region_single_attachment C.toSimpleGraph S C.connected_toSimpleGraph hS hmaxS) F = v ∧
        yr ∈ componentRegion F Set.univ) : HasAdmissiblePaths G x y k := by
  subst y
  classical
  by_contra hno
  let hCar := maximal_twoConnected_region_single_attachment C.toSimpleGraph S C.connected_toSimpleGraph hS hmaxS
  obtain ⟨T, U, hTU, hBT, hTS, hUS, Z0, Z1, hZ0, hZ1, hZ0T, hZ1U, hZ0B⟩ :=
    actual_hub_sides_produce_connectors C.toSimpleGraph S hCar C.connected_toSimpleGraph
      u v huv I b yr hI E hEu hIE hySide
  have hyI : yr ∉ I := by
    intro hy
    exact Set.disjoint_left.mp hTU (hBT (Or.inr hy)) (hZ1U yr Z1.end_mem_support)
  have hr := casebi_feasible_second_side_rigidity G A B x (componentVertex C yr) s k hmax hBs hk
    hG htri hquad hd hno ih C yr rfl I b hI hyI
  have hxB : x ∈ B := hmax.1.2.2.1
  obtain ⟨a, haB, hax⟩ := Set.exists_ne_of_one_lt_ncard
    (by have hh := hmax.1.2.2.2.2.1; omega : 1 < B.ncard) x
  have hB : B = ({x, a} : Set V) := by
    symm
    apply Set.eq_of_subset_of_ncard_le (show ({x, a} : Set V) ⊆ B from by
      rintro z (he | he)
      · exact Eq.mpr (congrArg (fun z : V => z ∈ B) he) hxB
      · exact Eq.mpr (congrArg (fun z : V => z ∈ B) he) haB)
    rw [Set.ncard_pair hax.symm]
    have hs1 := hr.1
    omega
  have hB' : B = ({a, x} : Set V) := by rw [hB]; exact Set.pair_comm x a
  let D := componentRegion C (fragmentBlock I b)
  let H := componentRegion C S
  let T' := componentRegion C T
  let U' := componentRegion C U
  let m := k - 1
  let f : C.toSimpleGraph →g G := componentVertexHom C
  let l : G.Walk (componentVertex C b) (componentVertex C u.1) := Z0.map f
  let r : G.Walk (componentVertex C v.1) (componentVertex C yr) := Z1.map f
  have hmap : ∀ {d e : C.supp} (p : C.toSimpleGraph.Walk d e) z,
      z ∈ (p.map f).support ↔ ∃ w ∈ p.support, componentVertex C w = z := by
    intro d e p z
    simp only [Walk.support_map, List.mem_map]
    change (∃ w ∈ p.support, componentVertex C w = z) ↔
      ∃ w ∈ p.support, componentVertex C w = z
    rfl
  have hQ : ∀ K : Set C.supp, ∀ z ∈ componentRegion C K, z ∉ A ∪ B := by
    intro K z hz hzQ
    exact Set.disjoint_left.mp (componentRegion_disjoint C K) hz hzQ
  have hlt : ∀ z ∈ l.support, z ∈ T' := by
    intro z hz; obtain ⟨w, hw, he⟩ := (hmap Z0 z).mp hz
    exact ⟨w, (hZ0T w hw).1, he⟩
  have hru : ∀ z ∈ r.support, z ∈ U' := by
    intro z hz; obtain ⟨w, hw, he⟩ := (hmap Z1 z).mp hz
    exact ⟨w, hZ1U w hw, he⟩
  have hDT : D ⊆ T' := by
    rintro z ⟨w, hw, he⟩; exact ⟨w, hBT hw, he⟩
  have hTU' : Disjoint T' U' := by
    apply Set.disjoint_left.mpr
    rintro z ⟨w, hw, he⟩ ⟨t, ht, het⟩
    have htw : t = w := componentVertex_injective C (het.trans he.symm)
    exact Set.disjoint_left.mp hTU hw (Eq.mp (congrArg (fun t : C.supp => t ∈ U) htw) ht)
  have hmeetS : ∀ K : Set C.supp, ∀ e : C.supp,
      (∀ z ∈ K, z ∈ S → z = e) → ∀ z ∈ componentRegion C K,
        z ∈ H → z = componentVertex C e := by
    intro K e he z ⟨w, hw, hew⟩ ⟨t, ht, het⟩
    have htw : t = w := componentVertex_injective C (het.trans hew.symm)
    have hwS : w ∈ S := Eq.mp (congrArg (fun t : C.supp => t ∈ S) htw) ht
    exact hew.symm.trans (congrArg (componentVertex C) (he w hw hwS))
  have hTH := hmeetS T u.1 hTS
  have hUH := hmeetS U v.1 hUS
  have hlpath : l.IsPath := (Walk.isPath_map_iff_of_injective (componentVertex_injective C)).mpr hZ0
  have hrpath : r.IsPath := (Walk.isPath_map_iff_of_injective (componentVertex_injective C)).mpr hZ1
  obtain ⟨ap, dp, P, hP, hPD⟩ := casebi_actual_terminal_child_family G A B x (componentVertex C yr)
    x a s k hmax hBs hk hG htri hquad hd hno ih C yr rfl I b hI hyI hxB hB
  obtain ⟨an, dn, N, hN, hND⟩ := casebi_actual_terminal_child_family G A B x (componentVertex C yr)
    a x s k hmax hBs hk hG htri hquad hd hno ih C yr rfl I b hI hyI haB hB'
  have hDl : ∀ z ∈ l.support, z ∈ D → z = componentVertex C b := by
    intro z hz ⟨w, hw, he⟩
    obtain ⟨t, ht, het⟩ := (hmap Z0 z).mp hz
    have hwt : w = t := componentVertex_injective C (he.trans het.symm)
    have htB := Eq.mp (congrArg (fun w : C.supp => w ∈ fragmentBlock I b) hwt) hw
    exact het.symm.trans (congrArg (componentVertex C) (hZ0B t ht htB))
  have hFl : ∀ (z : V) (hzB : z ∈ B), ∀ i,
      ∀ R : Fin m → G.Walk z (componentVertex C b),
      (∀ i t, t ∈ (R i).support → t ∈ D ∨ t = z) →
      ∀ t ∈ (R i).support, t ∈ l.support → t = componentVertex C b := by
    intro z hzB i R hRD t htR htl
    rcases hRD i t htR with htD | he
    · exact hDl t htl htD
    · exact False.elim (hQ T t (hlt t htl)
        (Or.inr (Eq.mpr (congrArg (fun t : V => t ∈ B) he) hzB)))
  have hPL := admissible_family_append_fixed_tail G x (componentVertex C b) (componentVertex C u.1)
    m ap dp P l hP hlpath (fun i => hFl x hxB i P hPD)
  have hNL := admissible_family_append_fixed_tail G a (componentVertex C b) (componentVertex C u.1)
    m an dn N l hN hlpath (fun i => hFl a haB i N hND)
  let PL := fun i => (P i).append l
  let NL := fun i => (N i).append l
  have hFT : ∀ (z : V) (R : Fin m → G.Walk z (componentVertex C b)),
      (∀ i t, t ∈ (R i).support → t ∈ D ∨ t = z) →
      ∀ i t, t ∈ ((R i).append l).support → t ∈ T' ∨ t = z := by
    intro z R hRD i t ht
    rcases (Walk.mem_support_append_iff (R i) l).mp ht with htR | htl
    · exact (hRD i t htR).elim (fun h => Or.inl (hDT h)) Or.inr
    · exact Or.inl (hlt t htl)
  have hPLT := hFT x P hPD
  have hNLT := hFT a N hND
  have hm : 1 ≤ m := by dsimp [m]; omega
  by_cases hLow : ∀ w : S, w ≠ u → w ≠ v →
      (G.neighborSet (componentVertex C w.1) ∩ (A ∪ B)).ncard ≤ 1
  · obtain ⟨ah, dh, R, hR, hRH⟩ := maximal_hub_low_Q_original_family G (A ∪ B) x
      (componentVertex C yr) k hk (Or.inr hxB) C yr rfl S u v huv hS hmaxS hcut hyS hLow hd ih
    have hRr : ∀ j z, z ∈ (R j).support → z ∈ r.support → z = componentVertex C v.1 :=
      fun j z hzR hzr => hUH z (hru z hzr) (hRH j z hzR)
    have hRR := admissible_family_append_fixed_tail G (componentVertex C u.1)
      (componentVertex C v.1) (componentVertex C yr) m ah dh R r hR hrpath hRr
    let RR := fun j => (R j).append r
    have hmeet : ∀ i j z, z ∈ (PL i).support → z ∈ (RR j).support → z = componentVertex C u.1 := by
      intro i j z hzP hzR
      rcases hPLT i z hzP with hzT | he
      · rcases hRR.2 j z hzR with hzH | hzU
        · exact hTH z hzT (hRH j z hzH)
        · exact False.elim (Set.disjoint_left.mp hTU' hzT (hru z hzU))
      · rcases hRR.2 j z hzR with hzH | hzU
        · exact False.elim (hQ S z (hRH j z hzH)
            (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ B) he) hxB)))
        · exact False.elim (hQ U z (hru z hzU)
            (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ B) he) hxB)))
    have hall := admissible_path_concatenation (G := G) hm hm hPL.1.1
      (by have hh := hRR.1.1; omega : 1 ≤ ah + r.length) hPL.1.2.1 hRR.1.2.1
      (fun _ => componentVertex C u.1) PL (fun _ j => RR j)
      (fun i => (hPL.1.2.2 i).1) (fun _ j => (hRR.1.2.2 j).1)
      (fun i => (hPL.1.2.2 i).2) (fun _ j => (hRR.1.2.2 j).2) hmeet
    exact hno (has_admissible_initial_segment (by dsimp [m]; omega : k ≤ m + m - 1) hall)
  · have hex : ∃ w : S, w ≠ u ∧ w ≠ v ∧
        2 ≤ (G.neighborSet (componentVertex C w.1) ∩ (A ∪ B)).ncard := by
      by_contra hn
      apply hLow
      intro w hwu hwv
      by_contra hh
      exact hn ⟨w, hwu, hwv, by omega⟩
    obtain ⟨w, hwu, hwv, hhigh⟩ := hex
    have hwy : componentVertex C w.1 ≠ componentVertex C yr := by
      intro he
      have hwyr : w.1 = yr := componentVertex_injective C he
      have hyr := Eq.mp (congrArg (fun z : C.supp => z ∈ S) hwyr) w.2
      exact hwv (Subtype.ext (hwyr.trans (hyS hyr)))
    have hw : componentVertex C w.1 ∉ (A ∪ B) ∪ {componentVertex C yr} := by
      rintro (hwQ | he)
      · exact w.1.1.2 hwQ
      · exact hwy he
    obtain ⟨_htwo, ds, L, hL, hLQ⟩ := casebi_hub_nonroot_two_neighbors_short_family
      G A B x (componentVertex C yr) a (componentVertex C w.1) hmax hB hax.symm htri hquad hw hhigh
    obtain ⟨K, hK, hKH⟩ := actual_hub_deleted_nonroot_bypass G (A ∪ B) C S hS u v w hwu.symm hwv.symm
    have hKr : ∀ z ∈ K.support, z ∈ r.support → z = componentVertex C v.1 :=
      fun z hzK hzr => hUH z (hru z hzr) (hKH z hzK).1
    let KR := K.append r
    have hKR : KR.IsPath := append_isPath_of_only_common_endpoint hK hrpath hKr
    have hNLKR : ∀ j z, z ∈ (NL j).support → z ∈ KR.support → z = componentVertex C u.1 := by
      intro j z hzN hzKR
      rcases hNLT j z hzN with hzT | he
      · rcases (Walk.mem_support_append_iff K r).mp hzKR with hzK | hzr
        · exact hTH z hzT (hKH z hzK).1
        · exact False.elim (Set.disjoint_left.mp hTU' hzT (hru z hzr))
      · rcases (Walk.mem_support_append_iff K r).mp hzKR with hzK | hzr
        · exact False.elim (hQ S z (hKH z hzK).1
            (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ B) he) haB)))
        · exact False.elim (hQ U z (hru z hzr)
            (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ B) he) haB)))
    have hNY := admissible_family_append_fixed_tail G a (componentVertex C u.1)
      (componentVertex C yr) m (an + l.length) dn NL KR hNL.1 hKR hNLKR
    let NY := fun j => (NL j).append KR
    have hNYQ : ∀ j z, z ∈ (NY j).support → z ∈ A ∪ B → z = a := by
      intro j z hz hzQ
      rcases hNY.2 j z hz with hzN | hzKR
      · rcases hNLT j z hzN with hzT | he
        · exact False.elim (hQ T z hzT hzQ)
        · exact he
      · rcases (Walk.mem_support_append_iff K r).mp hzKR with hzK | hzr
        · exact False.elim (hQ S z (hKH z hzK).1 hzQ)
        · exact False.elim (hQ U z (hru z hzr) hzQ)
    have hwH : componentVertex C w.1 ∈ H := ⟨w.1, w.2, rfl⟩
    have hNYw : ∀ j, componentVertex C w.1 ∉ (NY j).support := by
      intro j hwN
      rcases hNY.2 j (componentVertex C w.1) hwN with hwNL | hwKR
      · rcases hNLT j (componentVertex C w.1) hwNL with hwT | he
        · exact hwu (Subtype.ext (componentVertex_injective C (hTH _ hwT hwH)))
        · exact w.1.1.2 (Or.inr (Eq.mpr (congrArg (fun z : V => z ∈ B) he) haB))
      · rcases (Walk.mem_support_append_iff K r).mp hwKR with hwK | hwr
        · exact (hKH _ hwK).2 rfl
        · exact hwv (Subtype.ext (componentVertex_injective C (hUH _ (hru _ hwr) hwH)))
    have hmeet : ∀ i j z, z ∈ (L i).support → z ∈ (NY j).support → z = a := by
      intro i j z hzL hzN
      rcases hLQ i z hzL with hzQ | he
      · exact hNYQ j z hzN hzQ
      · exact False.elim (hNYw j (Eq.mp (congrArg (fun z : V => z ∈ (NY j).support) he) hzN))
    have hall := admissible_path_concatenation (G := G) (by omega : 1 ≤ 2) hm hL.1
      (by have hh := hNY.1.1; omega : 1 ≤ an + l.length + KR.length) hL.2.1 hNY.1.2.1
      (fun _ => a) L (fun _ j => NY j) (fun i => (hL.2.2 i).1)
      (fun _ j => (hNY.1.2.2 j).1) (fun i => (hL.2.2 i).2)
      (fun _ j => (hNY.1.2.2 j).2) hmeet
    exact hno (has_admissible_initial_segment (by dsimp [m]; omega : k ≤ 2 + m - 1) hall)

#print axioms actual_maximal_hub_sides_original_contradiction
end TaskH.Gao
