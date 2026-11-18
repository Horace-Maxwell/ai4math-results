import Research.TaskH.Gao.TerminalFragmentExistence
import Research.TaskH.Gao.GraphIsoTwoConnected

/-! Exact transport out of an actual component of G-K. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u} {G : SimpleGraph V} {K : Set V}

def componentVertex (C : (G.induce Kᶜ).ConnectedComponent) (v : C.supp) : V := v.1.1

def componentRegion (C : (G.induce Kᶜ).ConnectedComponent) (I : Set C.supp) : Set V :=
  {z | ∃ v : C.supp, v ∈ I ∧ componentVertex C v = z}

theorem componentVertex_injective (C : (G.induce Kᶜ).ConnectedComponent) :
    Function.Injective (componentVertex C) := by
  intro a b he
  apply Subtype.ext
  exact Subtype.ext he

def componentVertexHom (C : (G.induce Kᶜ).ConnectedComponent) : C.toSimpleGraph →g G where
  toFun := componentVertex C
  map_rel' := fun h => h

theorem componentRegion_disjoint (C : (G.induce Kᶜ).ConnectedComponent) (I : Set C.supp) :
    Disjoint (componentRegion C I) K := by
  apply Set.disjoint_left.mpr
  rintro z ⟨v, _hv, he⟩ hz
  have he' : v.1.1 = z := he
  exact v.1.2 (Eq.mpr (congrArg (fun t : V => t ∈ K) he') hz)

noncomputable def componentRegionGraphIso (C : (G.induce Kᶜ).ConnectedComponent)
    (I : Set C.supp) : C.toSimpleGraph.induce I ≃g G.induce (componentRegion C I) where
  toEquiv := Equiv.ofBijective
    (fun v : I => (⟨componentVertex C v.1, v.1, v.2, rfl⟩ : componentRegion C I)) (by
      constructor
      · intro a b he
        have hv : componentVertex C a.1 = componentVertex C b.1 :=
          congrArg (fun z : componentRegion C I => z.1) he
        exact Subtype.ext (componentVertex_injective C hv)
      · rintro ⟨z, v, hv, he⟩
        exact ⟨⟨v, hv⟩, Subtype.ext he⟩)
  map_rel_iff' := by intro a b; rfl

theorem component_fragment_original_cover (C : (G.induce Kᶜ).ConnectedComponent)
    (I : Set C.supp) (b : C.supp) (h : TerminalFragment C.toSimpleGraph I b) :
    ∀ a ∈ componentRegion C (fragmentBlock I b), a ≠ componentVertex C b →
      ∀ z, G.Adj a z → z ∈ componentRegion C (fragmentBlock I b) ∨ z ∈ K := by
  rintro a ⟨v, hv, he⟩ hab z haz
  have hvb : v ≠ b := fun he' => hab (he.symm.trans (congrArg (componentVertex C) he'))
  have hvI : v ∈ I := by
    rcases hv with hv | hv
    · exact False.elim (hvb hv)
    · exact hv
  by_cases hzK : z ∈ K
  · exact Or.inr hzK
  · have he' : v.1.1 = a := he
    have evG : G.Adj v.1.1 z :=
      Eq.mpr (congrArg (fun t : V => G.Adj t z) he') haz
    let zr : C.supp := ⟨⟨z, hzK⟩, C.mem_supp_of_adj_mem_supp v.2 evG⟩
    have evz : C.toSimpleGraph.Adj v zr := evG
    rcases h.2.2.1 v hvI zr evz with hzb | hzI
    · exact Or.inl ⟨zr, Or.inl hzb, rfl⟩
    · exact Or.inl ⟨zr, Or.inr hzI, rfl⟩

theorem component_fragment_y_boundary (C : (G.induce Kᶜ).ConnectedComponent)
    (I : Set C.supp) (b y : C.supp) (hy : y ∉ I) :
    componentVertex C y ∈ componentRegion C (fragmentBlock I b) →
      componentVertex C y = componentVertex C b := by
  rintro ⟨v, hv, he⟩
  have hvy : v = y := componentVertex_injective C he
  subst v
  rcases hv with hyb | hyI
  · exact congrArg (componentVertex C) hyb
  · exact False.elim (hy hyI)

#print axioms componentVertex
#print axioms componentRegion
#print axioms componentVertex_injective
#print axioms componentVertexHom
#print axioms componentRegion_disjoint
#print axioms componentRegionGraphIso
#print axioms component_fragment_original_cover
#print axioms component_fragment_y_boundary
end TaskH.Gao
