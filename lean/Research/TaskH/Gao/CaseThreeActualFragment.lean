import Research.TaskH.Gao.CaseThreeKBlock
import Research.TaskH.Gao.ComponentTerminalTail
import Research.TaskH.Gao.Base

/-! A real original terminal fragment has non-singleton interior in the Case3 counterexample. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem case3_actual_terminal_interior_two [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (k : ℕ)
    (C : (G.induce (insert x (insert p (insert q K)))ᶜ).ConnectedComponent)
    [Fintype C.supp] (I : Set C.supp) (b yr : C.supp)
    (hY : componentVertex C yr = y)
    (hterm : TerminalFragment C.toSimpleGraph I b) (hy : yr ∉ I)
    (hK : Maximal (fun L : Set V => G.IsClique L ∧ L ⊆ case3CoreDomain G x y p q) K)
    (ht : 2 ≤ K.ncard) (htk : K.ncard < k)
    (hix : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k)
    (R : G.Walk (componentVertex C b) y) (hR : R.IsPath)
    (hRT : ∀ z ∈ R.support, z ∉ insert x (insert p (insert q K)))
    (hRB : ∀ z ∈ R.support, z ∈ componentRegion C (fragmentBlock I b) → z = componentVertex C b) :
    2 ≤ I.ncard := by
  classical
  by_contra hsmall
  have hpos : 0 < I.ncard := (Set.ncard_pos (Set.toFinite I)).mpr hterm.1
  have hone : I.ncard = 1 := by omega
  obtain ⟨a, hIa⟩ := Set.ncard_eq_one.mp hone
  have ha : a ∈ I := by rw [hIa]; exact Set.mem_singleton a
  have hab : a ≠ b := fun he => hterm.2.1 (Eq.mp (congrArg (fun v : C.supp => v ∈ I) he) ha)
  have habV : componentVertex C a ≠ componentVertex C b := fun he => hab (componentVertex_injective C he)
  let B := componentRegion C (fragmentBlock I b)
  have haB : componentVertex C a ∈ B := ⟨a, Or.inr ha, rfl⟩
  have hBC : Disjoint B (insert x (insert p (insert q K))) := componentRegion_disjoint C (fragmentBlock I b)
  have hcover := component_fragment_original_cover C I b hterm
  have hNB : G.neighborSet (componentVertex C a) ∩ B ⊆ {componentVertex C b} := by
    rintro z ⟨eaz, w, hw, he⟩
    change z = componentVertex C b
    rcases hw with hwb | hwI
    · exact he.symm.trans (congrArg (componentVertex C) hwb)
    · have hwa : w = a := by simpa only [hIa, Set.mem_singleton_iff] using hwI
      have hza : z = componentVertex C a := he.symm.trans (congrArg (componentVertex C) hwa)
      exact False.elim (G.irrefl (Eq.mp (congrArg (fun v : V => G.Adj (componentVertex C a) v) hza) eaz))
  have hNBcard : (G.neighborSet (componentVertex C a) ∩ B).ncard ≤ 1 := by
    simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hNB
  have haT : componentVertex C a ∉ insert x (insert p (insert q K)) := a.1.2
  have hax : componentVertex C a ≠ x := fun he => haT (Or.inl he)
  have hap : componentVertex C a ≠ p := fun he => haT (Or.inr (Or.inl he))
  have haq : componentVertex C a ≠ q := fun he => haT (Or.inr (Or.inr (Or.inl he)))
  have haK : componentVertex C a ∉ K := fun hh => haT (Or.inr (Or.inr (Or.inr hh)))
  have hay : componentVertex C a ≠ y := by
    intro he
    have haYr : a = yr := componentVertex_injective C (he.trans hY.symm)
    exact hy (Eq.mp (congrArg (fun v : C.supp => v ∈ I) haYr) ha)
  have hcap := case3_actual_core_loss_budget G x y p q K hK ht hix exp exq hpq
    (componentVertex C a) hax hay hap haq haK
  rw [← case3_core_reorder K x p q] at hcap
  have hpart := disjoint_region_neighbor_partition G B (insert x (insert p (insert q K))) hBC
    (componentVertex C a) (hcover (componentVertex C a) haB habV)
  have hdOrig := hd (componentVertex C a) hax hay
  have htouch : ∃ u ∈ K, G.Adj (componentVertex C a) u := by
    by_contra hn
    have hb : collapsedNeighborCount G K (componentVertex C a) = 0 := by
      unfold collapsedNeighborCount
      exact ite_eq_right hn
    rw [hb] at hcap
    omega
  have hbit : collapsedNeighborCount G K (componentVertex C a) = 1 := by
    unfold collapsedNeighborCount
    exact ite_eq_left htouch
  rw [hbit] at hcap
  have hcount : k ≤ K.ncard + 1 := by omega
  obtain ⟨u, huK, eau⟩ := htouch
  have htermA : TerminalFragment C.toSimpleGraph {a} b :=
    Eq.mp (congrArg (fun J : Set C.supp => TerminalFragment C.toSimpleGraph J b) hIa) hterm
  obtain ⟨eab, _hbridge, _hneighbors, _hblock⟩ :=
    terminalFragment_singleton_bridge C.toSimpleGraph a b C.connected_toSimpleGraph htermA
  have eabG : G.Adj (componentVertex C a) (componentVertex C b) := eab
  have haR : componentVertex C a ∉ R.support := fun hh => habV (hRB _ hh haB)
  have hinner : (Walk.cons eabG R).IsPath := hR.cons haR
  have huT : u ∈ insert x (insert p (insert q K)) := Or.inr (Or.inr (Or.inr huK))
  have huInner : u ∉ (Walk.cons eabG R).support := by
    rw [Walk.support_cons]
    intro hh
    rcases List.mem_cons.mp hh with he | hh
    · exact haT (Eq.mp (congrArg (fun v : V => v ∈ insert x (insert p (insert q K))) he) huT)
    · exact hRT u hh huT
  let tail : G.Walk u y := Walk.cons eau.symm (Walk.cons eabG R)
  have htail : tail.IsPath := hinner.cons huInner
  have htailCore : ∀ z ∈ tail.support, z ∈ insert x (insert p (insert q K)) → z = u := by
    intro z hz hzT
    change z ∈ u :: componentVertex C a :: R.support at hz
    rcases List.mem_cons.mp hz with he | hz
    · exact he
    · rcases List.mem_cons.mp hz with he | hz
      · exact False.elim (haT (Eq.mp (congrArg (fun v : V => v ∈ insert x (insert p (insert q K))) he) hzT))
      · exact False.elim (hRT z hz hzT)
  obtain ⟨c, hc, hcsupp⟩ := case3_core_member_family G x y p q K hK.1.1 hK.1.2 ht exp exq hpq u huK
  have hmeet : ∀ i z, z ∈ (c i).support → z ∈ tail.support → z = u := by
    intro i z hz hzTail
    exact htailCore z hzTail (hcsupp i z hz)
  have hout := admissible_family_append_fixed_tail G x u y (K.ncard + 1) 2 1 c tail hc htail hmeet
  have hfamily : HasAdmissiblePaths G x y (K.ncard + 1) :=
    ⟨2 + tail.length, 1, (fun i => (c i).append tail), hout.1⟩
  exact hno (has_admissible_initial_segment hcount hfamily)

theorem case3_actual_component_block [Fintype V] (G : SimpleGraph V)
    (x y p q : V) (K : Set V) (k : ℕ)
    (C : (G.induce (insert x (insert p (insert q K)))ᶜ).ConnectedComponent)
    [Fintype C.supp] (yr : C.supp) (hY : componentVertex C yr = y) (hC : 2 ≤ Fintype.card C.supp)
    (hK : Maximal (fun L : Set V => G.IsClique L ∧ L ⊆ case3CoreDomain G x y p q) K)
    (ht : 2 ≤ K.ncard) (htk : K.ncard < k) (hix : G.IsIndepSet (G.neighborSet x))
    (exp : G.Adj x p) (exq : G.Adj x q) (hpq : p ≠ q)
    (hd : NonrootDegreeAtLeast G x y (k + 1)) (hno : ¬HasAdmissiblePaths G x y k) :
    ∃ (B : Set V) (b : V), b ∈ B ∧ Disjoint B (insert x (insert p (insert q K))) ∧
      (y ∈ B → y = b) ∧
      (∀ v ∈ B, v ≠ b → ∀ z, G.Adj v z → z ∈ B ∨ z ∈ insert x (insert p (insert q K))) ∧
      (∃ iB : Fintype B, @TwoConnected B iB (G.induce B)) ∧
      ∃ R : G.Walk b y, R.IsPath ∧
        (∀ z ∈ R.support, z ∉ insert x (insert p (insert q K))) ∧
        ∀ z ∈ R.support, z ∈ B → z = b := by
  subst y
  classical
  obtain ⟨I, b, hterm, hy, R, hR, hRT, hRB⟩ := component_terminal_fragment_and_original_tail C yr hC
  let B := componentRegion C (fragmentBlock I b)
  let : Fintype (fragmentBlock I b) := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  have hI := case3_actual_terminal_interior_two G x (componentVertex C yr) p q K k C I b yr rfl
    hterm hy hK ht htk hix exp exq hpq hd hno R hR hRT hRB
  have hF := terminalFragment_twoConnected C.toSimpleGraph I b hterm hI
  have hB : TwoConnected (G.induce B) := twoConnected_of_graphIso
    (C.toSimpleGraph.induce (fragmentBlock I b)) (G.induce B)
    (componentRegionGraphIso C (fragmentBlock I b)) hF
  exact ⟨B, componentVertex C b, ⟨b, Or.inl rfl, rfl⟩,
    componentRegion_disjoint C (fragmentBlock I b), component_fragment_y_boundary C I b yr hy,
    component_fragment_original_cover C I b hterm, ⟨inferInstance, hB⟩, R, hR, hRT, hRB⟩

#print axioms case3_actual_terminal_interior_two
#print axioms case3_actual_component_block
end TaskH.Gao
