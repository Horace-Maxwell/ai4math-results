import Research.TaskH.Gao.CarrierCommonTerminalPoint

/-! Actual outside-component extraction yields a two-component cover and a
real bound on carrier cutpoints. Connectivity after deletion is constructed
from actual component walks and surviving spokes, not assumed as an oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem componentRegion_eq_of_common_original_point (G : SimpleGraph V)
    (S : Set V) (C D : (G.induce Sᶜ).ConnectedComponent) (p : V)
    (hpC : p ∈ componentRegion C Set.univ) (hpD : p ∈ componentRegion D Set.univ) : C = D := by
  obtain ⟨pc, _hpc, hec⟩ := hpC
  obtain ⟨pd, _hpd, hed⟩ := hpD
  have hev : componentVertex C pc = componentVertex D pd := hec.trans hed.symm
  have he : pc.1 = pd.1 := Subtype.ext hev
  have hD : pc.1 ∈ D.supp :=
    Eq.mpr (congrArg (fun z : {z : V // z ∉ S} => z ∈ D.supp) he) pd.2
  exact ConnectedComponent.eq_of_common_vertex pc.2 hD

theorem carrier_common_point_two_component_cover [Fintype V]
    (G : SimpleGraph V) (S : Set V) (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (y p : V)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (E Y : (G.induce Sᶜ).ConnectedComponent)
    (hpE : p ∈ componentRegion E Set.univ) (hyY : y ∈ componentRegion Y Set.univ) :
    ∀ D : (G.induce Sᶜ).ConnectedComponent, D = E ∨ D = Y := by
  classical
  intro D
  by_cases hyD : y ∈ componentRegion D Set.univ
  · exact Or.inr (componentRegion_eq_of_common_original_point G S D Y y hyD hyY)
  · have hpD := carrier_root_avoiding_component_contains_common_point G S hS hG y p hp D hyD
    exact Or.inl (componentRegion_eq_of_common_original_point G S D E p hpD hpE)

theorem carrier_delete_connected_of_no_detached_component
    (G : SimpleGraph V) (S : Set V) (hS : SingleAttachmentCarrier G S) (z : S)
    (hcore : ((G.induce S).induce {v : S | v ≠ z}).Connected)
    (hatt : ∀ C : (G.induce Sᶜ).ConnectedComponent,
      (carrierAttachment G S hS C).1 ≠ z.1) :
    (G.induce {v | v ≠ z.1}).Connected := by
  classical
  obtain ⟨r⟩ := hcore.nonempty
  have hrz : r.1.1 ≠ z.1 := fun he => r.2 (Subtype.ext he)
  let f : ((G.induce S).induce {v : S | v ≠ z}) →g G.induce {v | v ≠ z.1} :=
    { toFun := fun v => ⟨v.1.1, fun he => v.2 (Subtype.ext he)⟩
      map_rel' := fun e => e }
  have hall : ∀ v : {v : V // v ≠ z.1},
      (G.induce {v | v ≠ z.1}).Reachable v ⟨r.1.1, hrz⟩ := by
    intro v
    by_cases hvS : v.1 ∈ S
    · let vr : {v : S // v ≠ z} := ⟨⟨v.1, hvS⟩, fun he => v.2 (congrArg Subtype.val he)⟩
      exact (hcore vr r).map f
    · let C := (G.induce Sᶜ).connectedComponentMk ⟨v.1, hvS⟩
      let vr : C.supp := ⟨⟨v.1, hvS⟩, rfl⟩
      let a := carrierAttachment G S hS C
      have haz : a.1 ≠ z.1 := hatt C
      obtain ⟨w, eaw⟩ := carrierAttachment_spoke G S hS C
      let g : C.toSimpleGraph →g G.induce {v | v ≠ z.1} :=
        { toFun := fun q => ⟨componentVertex C q, by
            intro he
            exact q.1.2 (Eq.mpr (congrArg (fun v : V => v ∈ S) he) z.2)⟩
          map_rel' := fun e => e }
      have hfirst := (C.connected_toSimpleGraph vr w).map g
      have hlast : (G.induce {v | v ≠ z.1}).Reachable ⟨a.1, haz⟩ ⟨r.1.1, hrz⟩ := by
        let ar : {v : S // v ≠ z} := ⟨a, fun he => haz (congrArg Subtype.val he)⟩
        exact (hcore ar r).map f
      have hedge : (G.induce {v | v ≠ z.1}).Adj (g w) ⟨a.1, haz⟩ := eaw.symm
      exact hfirst.trans (hedge.reachable.trans hlast)
  refine { preconnected := ?_, nonempty := ⟨⟨r.1.1, hrz⟩⟩ }
  intro a b
  exact (hall a).trans (hall b).symm

theorem carrier_common_point_cut_in_two_attachments [Fintype V]
    (G : SimpleGraph V) (S : Set V) [Fintype S]
    (hS : SingleAttachmentCarrier G S) (hTwo : TwoConnected (G.induce S))
    (hG : G.Connected) (y p : V)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (E Y : (G.induce Sᶜ).ConnectedComponent)
    (hpE : p ∈ componentRegion E Set.univ) (hyY : y ∈ componentRegion Y Set.univ) :
    ∀ z ∈ S, ¬(G.induce {v | v ≠ z}).Connected →
      z = (carrierAttachment G S hS E).1 ∨ z = (carrierAttachment G S hS Y).1 := by
  classical
  intro z hz hbad
  by_contra hn
  have hzE : z ≠ (carrierAttachment G S hS E).1 := fun he => hn (Or.inl he)
  have hzY : z ≠ (carrierAttachment G S hS Y).1 := fun he => hn (Or.inr he)
  have hcover := carrier_common_point_two_component_cover G S hS hG y p hp E Y hpE hyY
  have hatt : ∀ C : (G.induce Sᶜ).ConnectedComponent,
      (carrierAttachment G S hS C).1 ≠ z := by
    intro C
    rcases hcover C with he | he
    · subst C
      exact hzE.symm
    · subst C
      exact hzY.symm
  exact hbad (carrier_delete_connected_of_no_detached_component G S hS ⟨z, hz⟩
    (hTwo.2.2 ⟨z, hz⟩) hatt)


theorem carrier_common_point_cut_ncard_le_two [Fintype V]
    (G : SimpleGraph V) (S : Set V) [Fintype S]
    (hS : SingleAttachmentCarrier G S) (hTwo : TwoConnected (G.induce S))
    (hG : G.Connected) (y p : V)
    (hp : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (E Y : (G.induce Sᶜ).ConnectedComponent)
    (hpE : p ∈ componentRegion E Set.univ) (hyY : y ∈ componentRegion Y Set.univ) :
    (S ∩ {z | ¬(G.induce {v | v ≠ z}).Connected}).ncard ≤ 2 := by
  have hsub : S ∩ {z | ¬(G.induce {v | v ≠ z}).Connected} ⊆
      ({(carrierAttachment G S hS E).1, (carrierAttachment G S hS Y).1} : Set V) := by
    intro z hz
    exact carrier_common_point_cut_in_two_attachments G S hS hTwo hG y p hp E Y hpE hyY
      z hz.1 hz.2
  have hh := Set.ncard_le_ncard hsub
  have hpair := Set.ncard_insert_le (carrierAttachment G S hS E).1
    ({(carrierAttachment G S hS Y).1} : Set V)
  rw [Set.ncard_singleton] at hpair
  exact hh.trans hpair

#print axioms componentRegion_eq_of_common_original_point
#print axioms carrier_common_point_two_component_cover
#print axioms carrier_delete_connected_of_no_detached_component
#print axioms carrier_common_point_cut_in_two_attachments
#print axioms carrier_common_point_cut_ncard_le_two
end TaskH.Gao
