import Research.TaskH.Gao.NoHubOutsideActualCarrier
import Research.TaskH.Gao.CarrierAttachments

/-! The actual outside component containing the genuine leaf is exactly that
singleton; its actual unique carrier attachment is the original leaf boundary. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem singleton_terminal_actual_leaf_component_attachment
    (G : SimpleGraph V) (hG : G.Connected) (y z : V)
    (hT : TerminalFragment G {y} z)
    (S : Set V) (hCar : SingleAttachmentCarrier G S) (hzS : z ∈ S)
    (Y : (G.induce Sᶜ).ConnectedComponent)
    (hyY : y ∈ componentRegion Y Set.univ) :
    componentRegion Y Set.univ = {y} ∧ (carrierAttachment G S hCar Y).1 = z := by
  obtain ⟨yr, _hyr, heyr⟩ := hyY
  let f : Y.toSimpleGraph →g G.induce {v | v ≠ z} :=
    { toFun := fun q => ⟨componentVertex Y q, fun he => q.1.2
        (Eq.mpr (congrArg (fun v : V => v ∈ S) he) hzS)⟩
      map_rel' := fun e => e }
  have hEq : componentRegion Y Set.univ = ({y} : Set V) := by
    apply Set.Subset.antisymm
    · rintro a ⟨ar, _har, hear⟩
      obtain ⟨q⟩ := (Y.connected_toSimpleGraph yr ar).map f
      have haY := terminal_walk_stays_without_boundary G {y} z hT q
        (show (f yr).1 ∈ ({y} : Set V) from heyr)
      exact Eq.mp (congrArg (fun v : V => v ∈ ({y} : Set V)) hear) haY
    · intro a ha
      exact Eq.mpr (congrArg (fun v : V => v ∈ componentRegion Y Set.univ)
        (show a = y from ha)) ⟨yr, Set.mem_univ yr, heyr⟩
  obtain ⟨eyz, _hb, _hn, _hB⟩ := terminalFragment_singleton_bridge G y z hG hT
  have eyrz : G.Adj (componentVertex Y yr) z :=
    Eq.mpr (congrArg (fun v : V => G.Adj v z) heyr) eyz
  have hzA : (⟨z, hzS⟩ : S) = carrierAttachment G S hCar Y :=
    carrierAttachment_unique G S hCar Y yr ⟨z, hzS⟩ eyrz
  exact ⟨hEq, (congrArg Subtype.val hzA).symm⟩

#print axioms singleton_terminal_actual_leaf_component_attachment
end TaskH.Gao
