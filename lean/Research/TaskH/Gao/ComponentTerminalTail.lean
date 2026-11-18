import Research.TaskH.Gao.ComponentFragmentTransport

/-! Finite terminal descent produces a real original-graph tail, not a tail premise. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u} {G : SimpleGraph V} {K : Set V}

theorem terminal_component_original_tail (C : (G.induce Kᶜ).ConnectedComponent)
    (I : Set C.supp) (b y : C.supp) (h : TerminalFragment C.toSimpleGraph I b) (hy : y ∉ I) :
    ∃ R : G.Walk (componentVertex C b) (componentVertex C y), R.IsPath ∧
      (∀ z ∈ R.support, z ∉ K) ∧
      ∀ z ∈ R.support, z ∈ componentRegion C (fragmentBlock I b) →
        z = componentVertex C b := by
  let F := C.toSimpleGraph.induce {v : C.supp | v ∉ I}
  let br : {v : C.supp // v ∉ I} := ⟨b, h.2.1⟩
  let yr : {v : C.supp // v ∉ I} := ⟨y, hy⟩
  have hcomp : F.Connected := h.2.2.2.2.1
  obtain ⟨p, hp⟩ := hcomp.exists_isPath br yr
  let f : F →g G := {
    toFun := fun v => componentVertex C v.1
    map_rel' := fun e => e }
  have hf : Function.Injective f := by
    intro a d he
    exact Subtype.ext (componentVertex_injective C he)
  let R : G.Walk (componentVertex C b) (componentVertex C y) := p.map f
  refine ⟨R, (Walk.isPath_map_iff_of_injective hf).mpr hp, ?_, ?_⟩
  · intro z hz
    change z ∈ (p.map f).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨v, _hv, he⟩ := List.mem_map.mp hz
    have hev : componentVertex C v.1 = z := he
    exact hev ▸ v.1.1.2
  · intro z hz hzB
    change z ∈ (p.map f).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨v, _hv, he⟩ := List.mem_map.mp hz
    obtain ⟨w, hw, hwe⟩ := hzB
    have hev : componentVertex C v.1 = z := he
    have hwv : w = v.1 := componentVertex_injective C (hwe.trans hev.symm)
    subst w
    rcases hw with hvb | hvI
    · exact hev.symm.trans (congrArg (componentVertex C) hvb)
    · exact False.elim (v.2 hvI)

theorem component_terminal_fragment_and_original_tail
    (C : (G.induce Kᶜ).ConnectedComponent) [Fintype C.supp] (y : C.supp)
    (hC : 2 ≤ Fintype.card C.supp) :
    ∃ (I : Set C.supp) (b : C.supp), TerminalFragment C.toSimpleGraph I b ∧ y ∉ I ∧
      ∃ R : G.Walk (componentVertex C b) (componentVertex C y), R.IsPath ∧
        (∀ z ∈ R.support, z ∉ K) ∧
        ∀ z ∈ R.support, z ∈ componentRegion C (fragmentBlock I b) →
          z = componentVertex C b := by
  classical
  obtain ⟨a, hay⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card C.supp) y
  let D := (C.toSimpleGraph.induce {v : C.supp | v ≠ y}).connectedComponentMk ⟨a, hay⟩
  obtain ⟨b, E, hsub, hterm⟩ := terminal_fragment_in_deleted_component
    C.toSimpleGraph y D C.connected_toSimpleGraph
  let I := deletedInterior C.toSimpleGraph b E
  have hy : y ∉ I := by
    intro hyI
    exact deletedInterior_root_not_mem C.toSimpleGraph y D (hsub hyI)
  exact ⟨I, b, hterm, hy, terminal_component_original_tail C I b y hterm hy⟩

#print axioms terminal_component_original_tail
#print axioms component_terminal_fragment_and_original_tail
end TaskH.Gao
