import Research.TaskH.Gao.TerminalCommonPointDeletedComponents
import Research.TaskH.Gao.CarrierPeeling

/-! A genuine one-attachment outside component contains a real terminal
fragment obtained by strict deletion descent. Thus a common terminal point
excludes a third outside component; no component cover is supplied. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem carrier_component_contains_deleted_component (G : SimpleGraph V)
    (S : Set V) (hS : SingleAttachmentCarrier G S)
    (C : (G.induce Sᶜ).ConnectedComponent) (v : C.supp) :
    ∃ D : (G.induce {z | z ≠ (carrierAttachment G S hS C).1}).ConnectedComponent,
      deletedInterior G (carrierAttachment G S hS C).1 D ⊆ componentRegion C Set.univ := by
  classical
  let a := carrierAttachment G S hS C
  have hva : componentVertex C v ≠ a.1 := by
    intro he
    exact v.1.2 (Eq.mpr (congrArg (fun z : V => z ∈ S) he) a.2)
  let D := (G.induce {z | z ≠ a.1}).connectedComponentMk ⟨componentVertex C v, hva⟩
  refine ⟨D, ?_⟩
  intro w hw
  obtain ⟨hwa, hwD⟩ := hw
  have hr : (G.induce {z | z ≠ a.1}).Reachable
      ⟨componentVertex C v, hva⟩ ⟨w, hwa⟩ :=
    ConnectedComponent.exact hwD.symm
  obtain ⟨p⟩ := hr
  let R : Set V := {a.1}
  have hRS : R ⊆ S := by
    intro z hz
    change z = a.1 at hz
    exact Eq.mpr (congrArg (fun z : V => z ∈ S) hz) a.2
  exact carrier_old_component_walk_stays G S R hS hRS C
    (show (carrierAttachment G S hS C).1 ∈ R from rfl) p
    (show componentVertex C v ∈ componentRegion C Set.univ from ⟨v, Set.mem_univ v, rfl⟩)

theorem carrier_component_contains_actual_terminal [Fintype V]
    (G : SimpleGraph V) (S : Set V) (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (C : (G.induce Sᶜ).ConnectedComponent) :
    ∃ (I : Set V) (b : V), TerminalFragment G I b ∧ I ⊆ componentRegion C Set.univ := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  let vr : C.supp := ⟨v, hv⟩
  obtain ⟨D, hD⟩ := carrier_component_contains_deleted_component G S hS C vr
  obtain ⟨b, E, hsub, hE⟩ := terminal_fragment_in_deleted_component G
    (carrierAttachment G S hS C).1 D hG
  exact ⟨deletedInterior G b E, b, hE, hsub.trans hD⟩

theorem carrier_root_avoiding_component_contains_common_point [Fintype V]
    (G : SimpleGraph V) (S : Set V) (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (y p : V)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hyC : y ∉ componentRegion C Set.univ) : p ∈ componentRegion C Set.univ := by
  obtain ⟨I, b, hT, hsub⟩ := carrier_component_contains_actual_terminal G S hS hG C
  exact hsub (hp I b hT (fun hyI => hyC (hsub hyI)))

theorem carrier_root_avoiding_outside_component_unique [Fintype V]
    (G : SimpleGraph V) (S : Set V) (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (y p : V)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (C D : (G.induce Sᶜ).ConnectedComponent)
    (hyC : y ∉ componentRegion C Set.univ) (hyD : y ∉ componentRegion D Set.univ) : C = D := by
  obtain ⟨pc, _hpc, hec⟩ :=
    carrier_root_avoiding_component_contains_common_point G S hS hG y p hp C hyC
  obtain ⟨pd, _hpd, hed⟩ :=
    carrier_root_avoiding_component_contains_common_point G S hS hG y p hp D hyD
  have hev : componentVertex C pc = componentVertex D pd := hec.trans hed.symm
  have hsub : pc.1 = pd.1 := Subtype.ext hev
  have hD : pc.1 ∈ D.supp := Eq.mpr (congrArg (fun z : {z : V // z ∉ S} => z ∈ D.supp) hsub) pd.2
  exact ConnectedComponent.eq_of_common_vertex pc.2 hD

#print axioms carrier_component_contains_deleted_component
#print axioms carrier_component_contains_actual_terminal
#print axioms carrier_root_avoiding_component_contains_common_point
#print axioms carrier_root_avoiding_outside_component_unique
end TaskH.Gao
