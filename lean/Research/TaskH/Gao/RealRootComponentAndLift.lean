import Research.TaskH.Gao.CliqueEmptyRealRoot
import Research.TaskH.Gao.TerminalFragmentExistence

/-! Full neighbor cover is derived from an actual component and its actual
terminal fragment. Lifting uses an injective ORIGINAL induced embedding. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def componentFragmentRegion (G : SimpleGraph V) (K : Set V)
    (C : (G.induce {v | v ∉ K}).ConnectedComponent) (I : Set C) (b : C) : Set V :=
  {v | ∃ a : C, a ∈ fragmentBlock I b ∧ a.1.1 = v}

noncomputable def componentFragmentGraphIso (G : SimpleGraph V) (K : Set V)
    (C : (G.induce {v | v ∉ K}).ConnectedComponent) (I : Set C) (b : C) :
    C.toSimpleGraph.induce (fragmentBlock I b) ≃g G.induce (componentFragmentRegion G K C I b) := by
  let f : fragmentBlock I b → componentFragmentRegion G K C I b :=
    fun a => ⟨a.1.1.1, a.1, a.2, rfl⟩
  have hi : Function.Injective f := by
    intro a d he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have hv : a.1.1.1 = d.1.1.1 :=
      congrArg (fun z : componentFragmentRegion G K C I b => z.1) he
    exact hv
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨a, ha, he⟩ := v.2
    exact ⟨⟨a, ha⟩, Subtype.ext he⟩
  exact { toEquiv := Equiv.ofBijective f ⟨hi, hs⟩, map_rel_iff' := by intro a d; rfl }

theorem componentFragment_disjoint (G : SimpleGraph V) (K : Set V)
    (C : (G.induce {v | v ∉ K}).ConnectedComponent) (I : Set C) (b : C) :
    Disjoint (componentFragmentRegion G K C I b) K := by
  apply Set.disjoint_left.mpr
  intro v hvB hvK
  obtain ⟨a, _ha, rfl⟩ := hvB
  exact a.1.2 hvK

theorem componentFragment_full_cover (G : SimpleGraph V) (K : Set V)
    (C : (G.induce {v | v ∉ K}).ConnectedComponent) (I : Set C) (b : C)
    (h : TerminalFragment C.toSimpleGraph I b) :
    ∀ v ∈ componentFragmentRegion G K C I b, v ≠ b.1.1 →
      ∀ w, G.Adj v w → w ∈ componentFragmentRegion G K C I b ∨ w ∈ K := by
  intro v hv hvb w e
  obtain ⟨a, ha, rfl⟩ := hv
  by_cases hwK : w ∈ K
  · exact Or.inr hwK
  · let t : {v : V // v ∉ K} := ⟨w, hwK⟩
    have ht : t ∈ C.supp := C.mem_supp_of_adj_mem_supp a.2 e
    let d : C := ⟨t, ht⟩
    have haI : a ∈ I := by
      rcases ha with he | he
      · exact False.elim (hvb (congrArg (fun z : C => z.1.1) he))
      · exact he
    have hd : d ∈ fragmentBlock I b := h.2.2.1 a haI d e
    exact Or.inl ⟨d, hd, rfl⟩

theorem componentFragment_twoConnected (G : SimpleGraph V) (K : Set V)
    (C : (G.induce {v | v ∉ K}).ConnectedComponent) (I : Set C) (b : C)
    [iC : Fintype C] [iF : Fintype (fragmentBlock I b)]
    [iB : Fintype (componentFragmentRegion G K C I b)]
    (h : TerminalFragment C.toSimpleGraph I b) (hI : 2 ≤ I.ncard) :
    @TwoConnected (componentFragmentRegion G K C I b) iB
      (G.induce (componentFragmentRegion G K C I b)) := by
  have hf := terminalFragment_twoConnected C.toSimpleGraph I b h hI
  exact twoConnected_of_graphIso (C.toSimpleGraph.induce (fragmentBlock I b))
    (G.induce (componentFragmentRegion G K C I b)) (componentFragmentGraphIso G K C I b) hf

def realRootLift (G : SimpleGraph V) (B : Set V) (x : V) (b : B)
    (p : (realRootGraph G B x).Walk (realRootPoint B x) (realRootBlockPoint B x b)) :
    G.Walk x b.1 := p.map (SimpleGraph.Embedding.induce (B ∪ {x})).toHom

theorem realRootLift_isPath (G : SimpleGraph V) (B : Set V) (x : V) (b : B)
    (p : (realRootGraph G B x).Walk (realRootPoint B x) (realRootBlockPoint B x b))
    (hp : p.IsPath) : (realRootLift G B x b p).IsPath := by
  change (p.map (SimpleGraph.Embedding.induce (B ∪ {x})).toHom).IsPath
  exact (Walk.isPath_map_iff_of_injective
    (f := (SimpleGraph.Embedding.induce (B ∪ {x})).toHom)
    (fun a d he => Subtype.ext he)).mpr hp

theorem realRootLift_length (G : SimpleGraph V) (B : Set V) (x : V) (b : B)
    (p : (realRootGraph G B x).Walk (realRootPoint B x) (realRootBlockPoint B x b)) :
    (realRootLift G B x b p).length = p.length := by
  let f : realRootGraph G B x →g G :=
    { toFun := Subtype.val, map_rel' := fun e => e }
  change (p.map f).length = p.length
  exact Walk.length_map f p

theorem realRootLift_support (G : SimpleGraph V) (B : Set V) (x : V) (b : B)
    (p : (realRootGraph G B x).Walk (realRootPoint B x) (realRootBlockPoint B x b)) :
    ∀ z ∈ (realRootLift G B x b p).support, z ∈ B ∨ z = x := by
  let f : realRootGraph G B x →g G :=
    { toFun := Subtype.val, map_rel' := fun e => e }
  intro z hz
  change z ∈ (p.map f).support at hz
  rw [Walk.support_map] at hz
  obtain ⟨w, _hw, he⟩ := List.mem_map.mp hz
  change w.1 = z at he
  rcases w.2 with hwB | hwx
  · exact Or.inl (he ▸ hwB)
  · exact Or.inr (he.symm.trans hwx)

theorem realRootLift_meets_clique_only_root (G : SimpleGraph V) (B K : Set V)
    (x : V) (b : B) (hBK : Disjoint B K)
    (p : (realRootGraph G B x).Walk (realRootPoint B x) (realRootBlockPoint B x b)) :
    ∀ z ∈ (realRootLift G B x b p).support, z ∈ K → z = x := by
  intro z hz hzK
  rcases realRootLift_support G B x b p z hz with hzB | hzx
  · exact False.elim (Set.disjoint_left.mp hBK hzB hzK)
  · exact hzx

theorem realRootLift_append_fixed_tail (G : SimpleGraph V) (B : Set V)
    (x y : V) (b : B)
    (p : (realRootGraph G B x).Walk (realRootPoint B x) (realRootBlockPoint B x b))
    (hp : p.IsPath) (R : G.Walk b.1 y) (hR : R.IsPath)
    (hRx : x ∉ R.support) (hRB : ∀ z ∈ R.support, z ∈ B → z = b.1) :
    ((realRootLift G B x b p).append R).IsPath ∧
      ((realRootLift G B x b p).append R).length = p.length + R.length := by
  refine ⟨isPath_append_of_support_intersection (realRootLift G B x b p) R
    (realRootLift_isPath G B x b p hp) hR ?_, ?_⟩
  · intro z hzP hzR
    rcases realRootLift_support G B x b p z hzP with hzB | hzx
    · exact hRB z hzR hzB
    · exact False.elim (hRx (hzx ▸ hzR))
  · rw [Walk.length_append, realRootLift_length]

#print axioms componentFragmentRegion
#print axioms componentFragmentGraphIso
#print axioms componentFragment_disjoint
#print axioms componentFragment_full_cover
#print axioms componentFragment_twoConnected
#print axioms realRootLift
#print axioms realRootLift_isPath
#print axioms realRootLift_length
#print axioms realRootLift_support
#print axioms realRootLift_meets_clique_only_root
#print axioms realRootLift_append_fixed_tail
end TaskH.Gao
