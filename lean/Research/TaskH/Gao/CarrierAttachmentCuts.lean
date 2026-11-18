import Research.TaskH.Gao.CarrierPeeling

/-! A real singleton attachment is an actual cut whenever another carrier point remains. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem carrierAttachment_cut (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (C : (G.induce Sᶜ).ConnectedComponent)
    (r : S) (hr : r ≠ carrierAttachment G S hS C) :
    ¬(G.induce {v | v ≠ (carrierAttachment G S hS C).1}).Connected := by
  intro hG
  let a := carrierAttachment G S hS C
  let T : Set V := {a.1}
  have hTS : T ⊆ S := by
    intro v hv
    change v = a.1 at hv
    exact Eq.mpr (congrArg (fun v : V => v ∈ S) hv) a.2
  have hr' : r.1 ≠ a.1 := fun he => hr (Subtype.ext he)
  obtain ⟨v, _eav⟩ := carrierAttachment_spoke G S hS C
  have hva : componentVertex C v ≠ a.1 := fun he => v.1.2
    (Eq.mpr (congrArg (fun v : V => v ∈ S) he) a.2)
  obtain ⟨p⟩ := hG ⟨componentVertex C v, hva⟩ ⟨r.1, hr'⟩
  have hrC := carrier_old_component_walk_stays G S T hS hTS C (show a.1 ∈ T from rfl) p
    (show componentVertex C v ∈ componentRegion C Set.univ from ⟨v, Set.mem_univ v, rfl⟩)
  exact Set.disjoint_left.mp (componentRegion_disjoint C Set.univ) hrC r.2

theorem singleAttachmentCarrier_order_three [Fintype V] (G : SimpleGraph V)
    (S : Set V) (hS : SingleAttachmentCarrier G S) (w y : V)
    (hw : w ∈ S) (hy : y ∈ S) (hwy : w ≠ y) (hV : 3 ≤ Fintype.card V)
    (hGw : (G.induce {v | v ≠ w}).Connected)
    (hGy : (G.induce {v | v ≠ y}).Connected) : 3 ≤ S.ncard := by
  classical
  by_contra hn
  have hpair : ({w, y} : Set V) ⊆ S := by
    rintro v (he | he)
    · exact Eq.mpr (congrArg (fun v : V => v ∈ S) he) hw
    · exact Eq.mpr (congrArg (fun v : V => v ∈ S) he) hy
  have htwo : 2 ≤ S.ncard := by
    simpa only [Set.ncard_pair hwy] using Set.ncard_le_ncard hpair
  have hcard : S.ncard = 2 := by omega
  have hSe : S = ({w, y} : Set V) := by
    symm
    exact Set.eq_of_subset_of_ncard_le hpair
      (le_of_eq (hcard.trans (Set.ncard_pair hwy).symm))
  have hout : ∃ v : V, v ∉ S := by
    by_contra h
    have he : S = Set.univ := Set.eq_univ_of_forall (by
      intro v
      by_contra hv
      exact h ⟨v, hv⟩)
    have hNat : 3 ≤ Nat.card V := by simpa only [Fintype.card_eq_nat_card] using hV
    rw [he, Set.ncard_univ] at hcard
    omega
  obtain ⟨v, hvS⟩ := hout
  let C := (G.induce Sᶜ).connectedComponentMk ⟨v, hvS⟩
  let a := carrierAttachment G S hS C
  have ha : a.1 = w ∨ a.1 = y := by
    have hh : a.1 ∈ ({w, y} : Set V) :=
      Eq.mp (congrArg (fun Q : Set V => a.1 ∈ Q) hSe) a.2
    exact hh
  rcases ha with haw | hay
  · have hra : (⟨y, hy⟩ : S) ≠ a := fun he => hwy
      (haw.symm.trans (congrArg Subtype.val he).symm)
    apply carrierAttachment_cut G S hS C ⟨y, hy⟩ hra
    change (G.induce {v | v ≠ a.1}).Connected
    rw [haw]
    exact hGw
  · have hra : (⟨w, hw⟩ : S) ≠ a := fun he => hwy
      ((congrArg Subtype.val he).trans hay)
    apply carrierAttachment_cut G S hS C ⟨w, hw⟩ hra
    change (G.induce {v | v ≠ a.1}).Connected
    rw [hay]
    exact hGy

#print axioms carrierAttachment_cut
#print axioms singleAttachmentCarrier_order_three
end TaskH.Gao
