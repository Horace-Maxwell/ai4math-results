import Research.TaskH.Gao.CarrierUniformTerminal
import Research.TaskH.Gao.TerminalFragmentCarrierRoute

/-!
Actual singleton-boundary components supply genuine terminal regions and
original simple exterior tails. Only the exact previously sealed generic
carrier-route parent is pending; the old casebi failed chain is not imported.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem carrier_terminal_in_actual_outside_component [Fintype V]
    (G : SimpleGraph V) (S : Set V) (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (C : (G.induce Sᶜ).ConnectedComponent) :
    ∃ (I : Set V) (b : V), TerminalFragment G I b ∧
      I ⊆ componentRegion C Set.univ ∧
      fragmentBlock I b ⊆ componentRegion C Set.univ ∪ {(carrierAttachment G S hS C).1} ∧
      ∃ P : G.Walk b (carrierAttachment G S hS C).1, P.IsPath ∧
        (∀ v ∈ P.support, v ∈ componentRegion C Set.univ ∪ {(carrierAttachment G S hS C).1} ∧ v ∉ I) ∧
        ∀ v ∈ P.support, v ∈ fragmentBlock I b → v = b := by
  classical
  let a := carrierAttachment G S hS C
  let D := componentRegion C Set.univ
  let T := D ∪ {a.1}
  obtain ⟨vr, _eav⟩ := carrierAttachment_spoke G S hS C
  have hva : componentVertex C vr ≠ a.1 := fun he => vr.1.2
    (Eq.mpr (congrArg (fun v : V => v ∈ S) he) a.2)
  let E := (G.induce {v | v ≠ a.1}).connectedComponentMk ⟨componentVertex C vr, hva⟩
  have hED : deletedInterior G a.1 E ⊆ D := by
    rintro z ⟨hza, hzE⟩
    obtain ⟨p⟩ := E.reachable_of_mem_supp (show
      (⟨componentVertex C vr, hva⟩ : {v : V // v ≠ a.1}) ∈ E.supp from rfl) hzE
    have hRS : ({a.1} : Set V) ⊆ S := by
      intro v hv
      exact Eq.mpr (congrArg (fun v : V => v ∈ S) hv) a.2
    exact carrier_old_component_walk_stays G S {a.1} hS hRS C rfl p
      (show componentVertex C vr ∈ componentRegion C Set.univ from ⟨vr, Set.mem_univ vr, rfl⟩)
  obtain ⟨b, F, hFE, hTerm⟩ := terminal_fragment_in_deleted_component G a.1 E hG
  let I := deletedInterior G b F
  have hID : I ⊆ D := hFE.trans hED
  have hIT : I ⊆ T := fun v hv => Or.inl (hID hv)
  have haI : a.1 ∉ I := fun ha =>
    Set.disjoint_left.mp (componentRegion_disjoint C Set.univ) (hID ha) a.2
  have hclosed : ∀ v ∈ T, v ≠ a.1 → ∀ d, G.Adj v d → d ∈ T := by
    rintro v (hvD | he) hva d evd
    · obtain ⟨u, _hu, heu⟩ := hvD
      have eud : G.Adj (componentVertex C u) d :=
        Eq.mpr (congrArg (fun v : V => G.Adj v d) heu) evd
      by_cases hdS : d ∈ S
      · exact Or.inr (congrArg Subtype.val (carrierAttachment_unique G S hS C u ⟨d, hdS⟩ eud))
      · let dr : C.supp := ⟨⟨d, hdS⟩, C.mem_supp_of_adj_mem_supp u.2 eud⟩
        exact Or.inl ⟨dr, Set.mem_univ dr, rfl⟩
    · exact False.elim (hva he)
  have hT : (G.induce T).Connected := TaskH.Fan.rootedSet_connected G T a.1 (Or.inr rfl) hclosed hG
  obtain ⟨hbT, P, hP, hPS, hPB⟩ := terminal_boundary_route_in_connected_carrier G T I b a.1
    hT hIT (Or.inr rfl) haI hTerm
  have hBT : fragmentBlock I b ⊆ T := by
    rintro v (he | hv)
    · exact Eq.mpr (congrArg (fun v : V => v ∈ T) he) hbT
    · exact hIT hv
  exact ⟨I, b, hTerm, hID, hBT, P, hP, hPS, hPB⟩

theorem carrier_dual_terminal_branches [Fintype V] (G : SimpleGraph V)
    (S : Set V) (hS : SingleAttachmentCarrier G S) (hG : G.Connected)
    (C D : (G.induce Sᶜ).ConnectedComponent)
    (hCD : (carrierAttachment G S hS C).1 ≠ (carrierAttachment G S hS D).1) :
    ∃ (I J : Set V) (b c : V), TerminalFragment G I b ∧ TerminalFragment G J c ∧
      Disjoint (fragmentBlock I b) (fragmentBlock J c) ∧
      ∃ (P : G.Walk b (carrierAttachment G S hS C).1)
        (R : G.Walk c (carrierAttachment G S hS D).1), P.IsPath ∧ R.IsPath ∧
        (∀ v ∈ P.support, v ∉ I) ∧ (∀ v ∈ R.support, v ∉ J) ∧
        (∀ v ∈ P.support, v ∉ R.support) ∧
        (∀ v ∈ P.support, v ∈ fragmentBlock I b → v = b) ∧
        (∀ v ∈ R.support, v ∈ fragmentBlock J c → v = c) ∧
        (∀ v ∈ P.support, v ∉ fragmentBlock J c) ∧
        (∀ v ∈ R.support, v ∉ fragmentBlock I b) := by
  classical
  have hne : C ≠ D := fun he => hCD (congrArg (fun C => (carrierAttachment G S hS C).1) he)
  have hRegions : Disjoint (componentRegion C Set.univ) (componentRegion D Set.univ) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨u, _hu, he⟩ ⟨v, _hv, hev⟩
    have huv : u.1 = v.1 := Subtype.ext (he.trans hev.symm)
    have hvC : v.1 ∈ C.supp := Eq.mp (congrArg (fun a : {v : V // v ∉ S} => a ∈ C.supp) huv) u.2
    exact hne (ConnectedComponent.eq_of_common_vertex hvC v.2)
  let TC := componentRegion C Set.univ ∪ {(carrierAttachment G S hS C).1}
  let TD := componentRegion D Set.univ ∪ {(carrierAttachment G S hS D).1}
  have hDis : Disjoint TC TD := by
    apply Set.disjoint_left.mpr
    rintro v (hvC | heC) (hvD | heD)
    · exact Set.disjoint_left.mp hRegions hvC hvD
    · exact Set.disjoint_left.mp (componentRegion_disjoint C Set.univ) hvC
        (Eq.mpr (congrArg (fun v : V => v ∈ S) heD) (carrierAttachment G S hS D).2)
    · exact Set.disjoint_left.mp (componentRegion_disjoint D Set.univ) hvD
        (Eq.mpr (congrArg (fun v : V => v ∈ S) heC) (carrierAttachment G S hS C).2)
    · exact hCD (heC.symm.trans heD)
  obtain ⟨I, b, hI, _hIC, hIB, P, hP, hPS, hPB⟩ := carrier_terminal_in_actual_outside_component G S hS hG C
  obtain ⟨J, c, hJ, _hJD, hJB, R, hR, hRS, hRB⟩ := carrier_terminal_in_actual_outside_component G S hS hG D
  have hIJ : Disjoint (fragmentBlock I b) (fragmentBlock J c) :=
    Set.disjoint_left.mpr (fun _ hvI hvJ => Set.disjoint_left.mp hDis (hIB hvI) (hJB hvJ))
  refine ⟨I, J, b, c, hI, hJ, hIJ, P, R, hP, hR, ?_, ?_, ?_, hPB, hRB, ?_, ?_⟩
  · intro v hv; exact (hPS v hv).2
  · intro v hv; exact (hRS v hv).2
  · intro v hvP hvR; exact Set.disjoint_left.mp hDis (hPS v hvP).1 (hRS v hvR).1
  · intro v hvP hvJ; exact Set.disjoint_left.mp hDis (hPS v hvP).1 (hJB hvJ)
  · intro v hvR hvI; exact Set.disjoint_left.mp hDis (hIB hvI) (hRS v hvR).1

#print axioms carrier_terminal_in_actual_outside_component
#print axioms carrier_dual_terminal_branches
end TaskH.Gao
