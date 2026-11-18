import Research.TaskH.Gao.TwoTerminalSeparatingCut

/-!
The cut vertex may itself be a prescribed endpoint. A real deleted component
on its far side is adjoined back to that endpoint, and both terminal regions
and both routes are internally selected from disjoint connected carriers.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem terminal_routes_from_cut_at_first_endpoint [Fintype V]
    (G : SimpleGraph V) (w y : V) (hyw : y ≠ w) (hG : G.Connected)
    (hcut : ¬(G.induce {v | v ≠ w}).Connected)
    (hyavoid : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I) :
    ∃ (I J : Set V) (b c : V),
      TerminalFragment G I b ∧ TerminalFragment G J c ∧
      Disjoint (fragmentBlock I b) (fragmentBlock J c) ∧
      ∃ (P : G.Walk b w) (R : G.Walk c y), P.IsPath ∧ R.IsPath ∧
        (∀ v ∈ P.support, v ∉ I) ∧ (∀ v ∈ R.support, v ∉ J) ∧
        (∀ v ∈ P.support, v ∉ R.support) ∧
        (∀ v ∈ P.support, v ∈ fragmentBlock I b → v = b) ∧
        (∀ v ∈ R.support, v ∈ fragmentBlock J c → v = c) ∧
        (∀ v ∈ P.support, v ∉ fragmentBlock J c) ∧
        (∀ v ∈ R.support, v ∉ fragmentBlock I b) := by
  classical
  let C := (G.induce {v | v ≠ w}).connectedComponentMk ⟨y, hyw⟩
  obtain ⟨D, hyD⟩ := exists_deleted_component_avoiding G w y hyw hcut
  have hDC : D ≠ C := by
    intro he
    apply hyD
    rw [he]
    exact ⟨hyw, rfl⟩
  let S := fragmentBlock (deletedInterior G w D) w
  let T := deletedInterior G w C
  have hDT := deletedInteriors_disjoint_of_components_ne G w D C hDC
  have hST : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro v hvS hvT
    rcases hvS with he | hvD
    · exact deletedInterior_root_not_mem G w C
        (Eq.mp (congrArg (fun v : V => v ∈ T) he) hvT)
    · exact Set.disjoint_left.mp hDT hvD hvT
  obtain ⟨b, E, hIS, hI⟩ := terminal_fragment_in_deleted_component G w D hG
  obtain ⟨c, F, hJT, hJ⟩ := terminal_fragment_in_deleted_component G w C hG
  let I := deletedInterior G b E
  let J := deletedInterior G c F
  have hwS : w ∈ S := Or.inl rfl
  have hyT : y ∈ T := ⟨hyw, rfl⟩
  have hwI : w ∉ I := fun hw => deletedInterior_root_not_mem G w D (hIS hw)
  have hyJ : y ∉ J := hyavoid J c hJ
  have hIS' : I ⊆ S := fun v hv => Or.inr (hIS hv)
  obtain ⟨hbS, P, hP, hPS, hPB⟩ := terminal_boundary_route_in_connected_carrier G S I b w
    (deletedBlock_connected G w D hG) hIS' hwS hwI hI
  obtain ⟨hcT, R, hR, hRT, hRB⟩ := terminal_boundary_route_in_connected_carrier G T J c y
    (deletedInterior_connected G w C) hJT hyT hyJ hJ
  have hBS : fragmentBlock I b ⊆ S := by
    intro v hv
    rcases hv with he | he
    · exact Eq.mpr (congrArg (fun v : V => v ∈ S) he) hbS
    · exact hIS' he
  have hBT : fragmentBlock J c ⊆ T := by
    intro v hv
    rcases hv with he | he
    · exact Eq.mpr (congrArg (fun v : V => v ∈ T) he) hcT
    · exact hJT he
  have hBB : Disjoint (fragmentBlock I b) (fragmentBlock J c) :=
    Set.disjoint_left.mpr (fun _ hvI hvJ => Set.disjoint_left.mp hST (hBS hvI) (hBT hvJ))
  refine ⟨I, J, b, c, hI, hJ, hBB, P, R, hP, hR, ?_, ?_, ?_, hPB, hRB, ?_, ?_⟩
  · intro v hv; exact (hPS v hv).2
  · intro v hv; exact (hRT v hv).2
  · intro v hvP hvR
    exact Set.disjoint_left.mp hST (hPS v hvP).1 (hRT v hvR).1
  · intro v hvP hvJ
    exact Set.disjoint_left.mp hST (hPS v hvP).1 (hBT hvJ)
  · intro v hvR hvI
    exact Set.disjoint_left.mp hST (hBS hvI) (hRT v hvR).1

#print axioms terminal_routes_from_cut_at_first_endpoint
end TaskH.Gao
