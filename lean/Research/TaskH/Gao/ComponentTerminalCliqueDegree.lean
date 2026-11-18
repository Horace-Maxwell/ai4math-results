import Research.TaskH.Gao.ComponentTerminalTail
import Research.TaskH.Gao.CliqueBoundaryBudget

/-! The singleton/bridge alternative is excluded by the actual maximal-clique degree budget. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u} {G : SimpleGraph V} {K : Set V}

theorem component_terminal_interior_at_least_two [Fintype V]
    (C : (G.induce Kᶜ).ConnectedComponent) [Fintype C.supp]
    (I : Set C.supp) (b y : C.supp) (x : V) (k : ℕ)
    (h : TerminalFragment C.toSimpleGraph I b) (hy : y ∉ I)
    (hK : Maximal G.IsClique K) (hx : x ∈ K) (htk : K.ncard ≤ k)
    (hdeg : NonrootDegreeAtLeast G x (componentVertex C y) (k + 1)) :
    2 ≤ I.ncard := by
  classical
  by_contra hsmall
  have hpos : 0 < I.ncard := (Set.ncard_pos (Set.toFinite I)).mpr h.1
  have hone : I.ncard = 1 := by omega
  obtain ⟨a, hIa⟩ := Set.ncard_eq_one.mp hone
  have ha : a ∈ I := by rw [hIa]; exact Set.mem_singleton a
  have hab : a ≠ b := fun he => h.2.1 (he ▸ ha)
  have habV : componentVertex C a ≠ componentVertex C b :=
    fun he => hab (componentVertex_injective C he)
  have hx' : componentVertex C a ≠ x := by
    intro he
    have he' : a.1.1 = x := he
    exact a.1.2 (Eq.mpr (congrArg (fun v : V => v ∈ K) he') hx)
  have hy' : componentVertex C a ≠ componentVertex C y := by
    intro he
    exact hy ((componentVertex_injective C he) ▸ ha)
  let B := componentRegion C (fragmentBlock I b)
  have hBK : Disjoint B K := componentRegion_disjoint C (fragmentBlock I b)
  have haB : componentVertex C a ∈ B := ⟨a, Or.inr ha, rfl⟩
  have hcover : ∀ z, G.Adj (componentVertex C a) z → z ∈ B ∨ z ∈ K :=
    component_fragment_original_cover C I b h _ haB habV
  have hsub : G.neighborSet (componentVertex C a) ∩ B ⊆ {componentVertex C b} := by
    rintro z ⟨haz, v, hv, he⟩
    change z = componentVertex C b
    rcases hv with hvb | hvI
    · exact he.symm.trans (congrArg (componentVertex C) hvb)
    · have hva : v = a := by simpa only [hIa, Set.mem_singleton_iff] using hvI
      have hza : z = componentVertex C a := he.symm.trans (congrArg (componentVertex C) hva)
      exact False.elim (G.irrefl (hza ▸ haz))
  have hBcard : (G.neighborSet (componentVertex C a) ∩ B).ncard ≤ 1 := by
    simpa only [Set.ncard_singleton] using Set.ncard_le_ncard hsub
  have hKcard := maximal_clique_external_neighbors_lt G K hK (componentVertex C a) a.1.2
  have hpartition := disjoint_region_neighbor_partition G B K hBK (componentVertex C a) hcover
  have hd := hdeg (componentVertex C a) hx' hy'
  omega

theorem component_terminal_block_twoConnected [Fintype V]
    (C : (G.induce Kᶜ).ConnectedComponent) [iC : Fintype C.supp]
    (I : Set C.supp) (b y : C.supp) (x : V) (k : ℕ)
    [iF : Fintype (fragmentBlock I b)]
    [iB : Fintype (componentRegion C (fragmentBlock I b))]
    (h : TerminalFragment C.toSimpleGraph I b) (hy : y ∉ I)
    (hK : Maximal G.IsClique K) (hx : x ∈ K) (htk : K.ncard ≤ k)
    (hdeg : NonrootDegreeAtLeast G x (componentVertex C y) (k + 1)) :
    @TwoConnected (componentRegion C (fragmentBlock I b)) iB
      (G.induce (componentRegion C (fragmentBlock I b))) := by
  have htwo := component_terminal_interior_at_least_two C I b y x k h hy hK hx htk hdeg
  have hF : @TwoConnected (fragmentBlock I b) iF
      (C.toSimpleGraph.induce (fragmentBlock I b)) :=
    terminalFragment_twoConnected C.toSimpleGraph I b h htwo
  exact twoConnected_of_graphIso
    (V := fragmentBlock I b) (W := componentRegion C (fragmentBlock I b))
    (iV := iF) (iW := iB) (C.toSimpleGraph.induce (fragmentBlock I b))
    (G.induce (componentRegion C (fragmentBlock I b)))
    (componentRegionGraphIso C (fragmentBlock I b)) hF

theorem actual_clique_component_fragment_tail [Fintype V]
    (C : (G.induce Kᶜ).ConnectedComponent) [Fintype C.supp] (y : C.supp)
    (hC : 2 ≤ Fintype.card C.supp) (x : V) (k : ℕ)
    (hK : Maximal G.IsClique K) (hx : x ∈ K) (htk : K.ncard ≤ k)
    (hdeg : NonrootDegreeAtLeast G x (componentVertex C y) (k + 1)) :
    ∃ (B : Set V) (b : V), b ∈ B ∧ Disjoint B K ∧
      (componentVertex C y ∈ B → componentVertex C y = b) ∧
      (∀ a ∈ B, a ≠ b → ∀ z, G.Adj a z → z ∈ B ∨ z ∈ K) ∧
      (∃ iB : Fintype B, @TwoConnected B iB (G.induce B)) ∧
      ∃ R : G.Walk b (componentVertex C y), R.IsPath ∧
        (∀ z ∈ R.support, z ∉ K) ∧ ∀ z ∈ R.support, z ∈ B → z = b := by
  classical
  obtain ⟨I, b, hterm, hy, R, hR, hRK, hRB⟩ :=
    component_terminal_fragment_and_original_tail C y hC
  let B := componentRegion C (fragmentBlock I b)
  let : Fintype (fragmentBlock I b) := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  have hB : TwoConnected (G.induce B) :=
    component_terminal_block_twoConnected C I b y x k hterm hy hK hx htk hdeg
  exact ⟨B, componentVertex C b, ⟨b, Or.inl rfl, rfl⟩,
    componentRegion_disjoint C (fragmentBlock I b),
    component_fragment_y_boundary C I b y hy,
    component_fragment_original_cover C I b hterm, ⟨inferInstance, hB⟩,
    R, hR, hRK, hRB⟩

#print axioms component_terminal_interior_at_least_two
#print axioms component_terminal_block_twoConnected
#print axioms actual_clique_component_fragment_tail
end TaskH.Gao
