import Research.TaskH.Gao.CarrierGreatestRegion

/-! Actual outside spokes give the reverse deletion-connectivity transport needed for uniform attachments. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem carrierAnchor_avoids_deleted (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V)
    (hall : ∀ C, (carrierAttachment G S hS C).1 ≠ z)
    (v : {v : V // v ≠ z}) : (carrierAnchor G S hS v.1).1 ≠ z := by
  classical
  by_cases hvS : v.1 ∈ S
  · rw [carrierAnchor_mem G S hS v.1 hvS]
    exact v.2
  · rw [carrierAnchor_outside G S hS v.1 hvS]
    exact hall _

theorem carrier_point_reaches_anchor_avoiding (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V) (hzS : z ∈ S)
    (v : {v : V // v ≠ z}) (ha : (carrierAnchor G S hS v.1).1 ≠ z) :
    (G.induce {v | v ≠ z}).Reachable v ⟨(carrierAnchor G S hS v.1).1, ha⟩ := by
  classical
  by_cases hvS : v.1 ∈ S
  · have hval : (carrierAnchor G S hS v.1).1 = v.1 :=
      congrArg (fun t : S => t.1) (carrierAnchor_mem G S hS v.1 hvS)
    have he : (⟨(carrierAnchor G S hS v.1).1, ha⟩ :
        {w : V // w ≠ z}) = v := Subtype.ext hval
    exact Eq.mpr
      (congrArg (fun t : {w : V // w ≠ z} =>
        (G.induce {w | w ≠ z}).Reachable v t) he) (Reachable.refl v)
  · let C := (G.induce Sᶜ).connectedComponentMk ⟨v.1, hvS⟩
    let vr : C.supp := ⟨⟨v.1, hvS⟩, rfl⟩
    let a := carrierAttachment G S hS C
    have haz : a.1 ≠ z := by
      simpa only [carrierAnchor_outside G S hS v.1 hvS] using ha
    obtain ⟨wr, eaw⟩ := carrierAttachment_spoke G S hS C
    let f : C.toSimpleGraph →g G.induce {v | v ≠ z} :=
      { toFun := fun u => ⟨componentVertex C u, fun he => u.1.2
          (Eq.mpr (congrArg (fun v : V => v ∈ S) he) hzS)⟩
        map_rel' := fun e => e }
    have hr := (C.connected_toSimpleGraph vr wr).map f
    have he : (G.induce {v | v ≠ z}).Adj (f wr) ⟨a.1, haz⟩ := eaw.symm
    have hFinal : (G.induce {v | v ≠ z}).Reachable v ⟨a.1, haz⟩ := hr.trans he.reachable
    simpa only [carrierAnchor_outside G S hS v.1 hvS] using hFinal

theorem carrier_global_deleted_connected (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V) (hzS : z ∈ S) (r : ↥(S \ {z} : Set V))
    (hall : ∀ C, (carrierAttachment G S hS C).1 ≠ z)
    (hflat : (G.induce (S \ {z})).Connected) :
    (G.induce {v | v ≠ z}).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨r.1, r.2.2⟩⟩ }
  intro v d
  have hv := carrierAnchor_avoids_deleted G S hS z hall v
  have hd := carrierAnchor_avoids_deleted G S hS z hall d
  let av : ↥(S \ {z} : Set V) := ⟨(carrierAnchor G S hS v.1).1, (carrierAnchor G S hS v.1).2, hv⟩
  let ad : ↥(S \ {z} : Set V) := ⟨(carrierAnchor G S hS d.1).1, (carrierAnchor G S hS d.1).2, hd⟩
  let f : G.induce (S \ {z}) →g G.induce {v | v ≠ z} :=
    { toFun := fun u => ⟨u.1, u.2.2⟩
      map_rel' := fun e => e }
  exact (carrier_point_reaches_anchor_avoiding G S hS z hzS v hv).trans
    (((hflat av ad).map f).trans
      (carrier_point_reaches_anchor_avoiding G S hS z hzS d hd).symm)

#print axioms carrierAnchor_avoids_deleted
#print axioms carrier_point_reaches_anchor_avoiding
#print axioms carrier_global_deleted_connected
end TaskH.Gao
