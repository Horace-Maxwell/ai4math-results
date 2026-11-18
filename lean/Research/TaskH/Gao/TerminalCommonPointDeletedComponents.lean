import Research.TaskH.Gao.TerminalRegionSeparation

/-! The actual strict terminal-fragment extraction forces uniqueness of a
non-root deleted component when all root-avoiding terminal interiors contain
one actual point. The common-point condition is explicitly local and is not
asserted here as an additional premise of the original Gao statement. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem terminal_common_point_in_deleted_component [Fintype V]
    (G : SimpleGraph V) (y p z : V) (hG : G.Connected)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (D : (G.induce {v | v ≠ z}).ConnectedComponent)
    (hyD : y ∉ deletedInterior G z D) : p ∈ deletedInterior G z D := by
  obtain ⟨b, E, hsub, hE⟩ := terminal_fragment_in_deleted_component G z D hG
  have hyE : y ∉ deletedInterior G b E := fun hy => hyD (hsub hy)
  exact hsub (hp (deletedInterior G b E) b hE hyE)

theorem terminal_common_point_deleted_component_unique [Fintype V]
    (G : SimpleGraph V) (y p z : V) (hG : G.Connected)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (D E : (G.induce {v | v ≠ z}).ConnectedComponent)
    (hyD : y ∉ deletedInterior G z D) (hyE : y ∉ deletedInterior G z E) : D = E := by
  obtain ⟨hpzD, hpD⟩ := terminal_common_point_in_deleted_component G y p z hG hp D hyD
  obtain ⟨hpzE, hpE⟩ := terminal_common_point_in_deleted_component G y p z hG hp E hyE
  have hpp : (⟨p, hpzD⟩ : {v : V // v ≠ z}) = ⟨p, hpzE⟩ := Subtype.ext rfl
  have hcomp : (G.induce {v | v ≠ z}).connectedComponentMk ⟨p, hpzD⟩ =
      (G.induce {v | v ≠ z}).connectedComponentMk ⟨p, hpzE⟩ :=
    congrArg (G.induce {v | v ≠ z}).connectedComponentMk hpp
  exact hpD.symm.trans (hcomp.trans hpE)

theorem terminal_common_point_deleted_component_dichotomy [Fintype V]
    (G : SimpleGraph V) (y p z : V) (hG : G.Connected)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (hyz : y ≠ z) (hpz : p ≠ z)
    (D : (G.induce {v | v ≠ z}).ConnectedComponent) :
    D = (G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩ ∨
      D = (G.induce {v | v ≠ z}).connectedComponentMk ⟨p, hpz⟩ := by
  classical
  by_cases hyD : y ∈ deletedInterior G z D
  · obtain ⟨h', he⟩ := hyD
    have hr : (⟨y, h'⟩ : {v : V // v ≠ z}) = ⟨y, hyz⟩ := Subtype.ext rfl
    left
    exact he.symm.trans (congrArg (G.induce {v | v ≠ z}).connectedComponentMk hr)
  · obtain ⟨h', he⟩ := terminal_common_point_in_deleted_component G y p z hG hp D hyD
    have hr : (⟨p, h'⟩ : {v : V // v ≠ z}) = ⟨p, hpz⟩ := Subtype.ext rfl
    right
    exact he.symm.trans (congrArg (G.induce {v | v ≠ z}).connectedComponentMk hr)

theorem terminal_common_point_delete_point_connected [Fintype V]
    (G : SimpleGraph V) (y p : V) (hG : G.Connected) (hyp : y ≠ p)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I) :
    (G.induce {v | v ≠ p}).Connected := by
  classical
  let K := G.induce {v | v ≠ p}
  have hall : ∀ D : K.ConnectedComponent, y ∈ deletedInterior G p D := by
    intro D
    by_contra hyD
    have hpD := terminal_common_point_in_deleted_component G y p p hG hp D hyD
    exact deletedInterior_root_not_mem G p D hpD
  have hmk : ∀ v : {v : V // v ≠ p},
      K.connectedComponentMk v = K.connectedComponentMk ⟨y, hyp⟩ := by
    intro v
    obtain ⟨hy', he⟩ := hall (K.connectedComponentMk v)
    have hyEq : (⟨y, hy'⟩ : {v : V // v ≠ p}) = ⟨y, hyp⟩ := Subtype.ext rfl
    exact he.symm.trans (congrArg K.connectedComponentMk hyEq)
  refine { preconnected := ?_, nonempty := ⟨⟨y, hyp⟩⟩ }
  intro a b
  exact ConnectedComponent.exact ((hmk a).trans (hmk b).symm)

#print axioms terminal_common_point_in_deleted_component
#print axioms terminal_common_point_deleted_component_unique
#print axioms terminal_common_point_deleted_component_dichotomy
#print axioms terminal_common_point_delete_point_connected
end TaskH.Gao
