import Research.TaskH.Gao.CasebiActualNoLeaf

/-! A genuinely selected feasible terminal block is ordinary two-connected. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem casebi_terminal_interior_two [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y)
    (I : Set C.supp) (b : C.supp) (hT : TerminalFragment C.toSimpleGraph I b)
    (hyI : yr ∉ I) : 2 ≤ I.ncard := by
  classical
  by_contra hn
  have hp : 0 < I.ncard := (Set.ncard_pos (Set.toFinite I)).mpr hT.1
  have he : I.ncard = 1 := by omega
  obtain ⟨a, hIa⟩ := Set.ncard_eq_one.mp he
  have haI : a ∈ I := by rw [hIa]; exact Set.mem_singleton a
  have hay : a ≠ yr := fun he => hyI (Eq.mp (congrArg (fun v : C.supp => v ∈ I) he) haI)
  have hTa : TerminalFragment C.toSimpleGraph {a} b :=
    Eq.mp (congrArg (fun J : Set C.supp => TerminalFragment C.toSimpleGraph J b) hIa) hT
  obtain ⟨_eab, _bridge, hNN, _hB⟩ :=
    terminalFragment_singleton_bridge C.toSimpleGraph a b C.connected_toSimpleGraph hTa
  have htwo := casebi_component_no_nonroot_leaf G A B x y s k hmax hBs hk htri hquad
    hd hno C yr hY a hay
  rw [hNN, Set.ncard_singleton] at htwo
  omega

theorem casebi_actual_feasible_block_exists [Fintype V] (G : SimpleGraph V)
    (A B : Set V) (x y : V) (s k : ℕ)
    (hmax : CasebiLexMax G x y A B) (hBs : B.ncard = s + 1) (hk : 3 ≤ k)
    (htri : CasebiNoRootTriangle G x y) (hquad : CasebiNoTripleOnRootQuad G x y)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (C : (G.induce (A ∪ B)ᶜ).ConnectedComponent) [Fintype C.supp]
    (yr : C.supp) (hY : componentVertex C yr = y) (hC : 2 ≤ Fintype.card C.supp) :
    ∃ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b ∧ yr ∉ I ∧
      2 ≤ I.ncard ∧
      (∃ iF : Fintype (componentRegion C (fragmentBlock I b)),
        @TwoConnected (componentRegion C (fragmentBlock I b)) iF
          (G.induce (componentRegion C (fragmentBlock I b)))) ∧
      ∃ R : G.Walk (componentVertex C b) y, R.IsPath ∧
        (∀ z ∈ R.support, z ∉ A ∪ B) ∧
        ∀ z ∈ R.support, z ∈ componentRegion C (fragmentBlock I b) → z = componentVertex C b := by
  subst y
  classical
  obtain ⟨I, b, hT, hyI, R, hR, hRQ, hRB⟩ :=
    component_terminal_fragment_and_original_tail C yr hC
  have hI := casebi_terminal_interior_two G A B x (componentVertex C yr) s k hmax hBs hk
    htri hquad hd hno C yr rfl I b hT hyI
  let D := componentRegion C (fragmentBlock I b)
  let : Fintype (fragmentBlock I b) := Fintype.ofFinite _
  let : Fintype D := Fintype.ofFinite _
  have hD : TwoConnected (G.induce D) := twoConnected_of_graphIso
    (C.toSimpleGraph.induce (fragmentBlock I b)) (G.induce D)
    (componentRegionGraphIso C (fragmentBlock I b))
    (terminalFragment_twoConnected C.toSimpleGraph I b hT hI)
  exact ⟨I, b, hT, hyI, hI, ⟨inferInstance, hD⟩, R, hR, hRQ, hRB⟩

#print axioms casebi_terminal_interior_two
#print axioms casebi_actual_feasible_block_exists
end TaskH.Gao
