import Research.TaskH.Gao.TerminalFragmentCarrierRoute

/-!
Two terminal regions and two disjoint actual routes are constructed by
strict terminal descent in two distinct components of an actual vertex
 deletion. This is the separating-cut subcase, not a full block-tree theorem.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem deletedInteriors_disjoint_of_components_ne (G : SimpleGraph V) (z : V)
    (C D : (G.induce {v | v ≠ z}).ConnectedComponent) (hCD : C ≠ D) :
    Disjoint (deletedInterior G z C) (deletedInterior G z D) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨hv, hvC⟩ ⟨_hv', hvD⟩
  exact hCD (hvC.symm.trans hvD)

theorem terminal_routes_across_actual_separating_cut [Fintype V]
    (G : SimpleGraph V) (w y z : V) (hwz : w ≠ z) (hyz : y ≠ z)
    (hG : G.Connected)
    (hsep : (G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩ ≠
      (G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩)
    (hwavoid : ∀ (I : Set V) (b : V), TerminalFragment G I b → w ∉ I)
    (hyavoid : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I) :
    ∃ (I J : Set V) (b c : V),
      TerminalFragment G I b ∧ TerminalFragment G J c ∧
      Disjoint (fragmentBlock I b) (fragmentBlock J c) ∧
      fragmentBlock I b ⊆ deletedInterior G z
        ((G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩) ∧
      fragmentBlock J c ⊆ deletedInterior G z
        ((G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩) ∧
      ∃ (P : G.Walk b w) (R : G.Walk c y), P.IsPath ∧ R.IsPath ∧
        (∀ v ∈ P.support, v ∈ deletedInterior G z
          ((G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩) ∧ v ∉ I) ∧
        (∀ v ∈ R.support, v ∈ deletedInterior G z
          ((G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩) ∧ v ∉ J) ∧
        (∀ v ∈ P.support, v ∉ R.support) ∧
        (∀ v ∈ P.support, v ∈ fragmentBlock I b → v = b) ∧
        (∀ v ∈ R.support, v ∈ fragmentBlock J c → v = c) ∧
        (∀ v ∈ P.support, v ∉ fragmentBlock J c) ∧
        (∀ v ∈ R.support, v ∉ fragmentBlock I b) := by
  classical
  let C := (G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩
  let D := (G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩
  let S := deletedInterior G z C
  let T := deletedInterior G z D
  have hST : Disjoint S T := deletedInteriors_disjoint_of_components_ne G z C D hsep
  have hwS : w ∈ S := ⟨hwz, rfl⟩
  have hyT : y ∈ T := ⟨hyz, rfl⟩
  obtain ⟨b, E, hIS, hI⟩ := terminal_fragment_in_deleted_component G z C hG
  obtain ⟨c, F, hJT, hJ⟩ := terminal_fragment_in_deleted_component G z D hG
  let I := deletedInterior G b E
  let J := deletedInterior G c F
  have hwI : w ∉ I := hwavoid I b hI
  have hyJ : y ∉ J := hyavoid J c hJ
  obtain ⟨hbS, P, hP, hPS, hPB⟩ := terminal_boundary_route_in_connected_carrier G S I b w
    (deletedInterior_connected G z C) hIS hwS hwI hI
  obtain ⟨hcT, R, hR, hRT, hRB⟩ := terminal_boundary_route_in_connected_carrier G T J c y
    (deletedInterior_connected G z D) hJT hyT hyJ hJ
  have hBS : fragmentBlock I b ⊆ S := by
    intro v hv
    rcases hv with he | he
    · exact Eq.mpr (congrArg (fun v : V => v ∈ S) he) hbS
    · exact hIS he
  have hBT : fragmentBlock J c ⊆ T := by
    intro v hv
    rcases hv with he | he
    · exact Eq.mpr (congrArg (fun v : V => v ∈ T) he) hcT
    · exact hJT he
  have hBB : Disjoint (fragmentBlock I b) (fragmentBlock J c) :=
    Set.disjoint_left.mpr (fun _ hvI hvJ => Set.disjoint_left.mp hST (hBS hvI) (hBT hvJ))
  refine ⟨I, J, b, c, hI, hJ, hBB, hBS, hBT, P, R, hP, hR, hPS, hRT, ?_,
    hPB, hRB, ?_, ?_⟩
  · intro v hvP hvR
    exact Set.disjoint_left.mp hST (hPS v hvP).1 (hRT v hvR).1
  · intro v hvP hvJ
    exact Set.disjoint_left.mp hST (hPS v hvP).1 (hBT hvJ)
  · intro v hvR hvI
    exact Set.disjoint_left.mp hST (hBS hvI) (hRT v hvR).1

#print axioms deletedInteriors_disjoint_of_components_ne
#print axioms terminal_routes_across_actual_separating_cut
end TaskH.Gao
