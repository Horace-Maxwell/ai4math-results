import Research.TaskH.Gao.CarrierCentralChoice

/-! The internally obtained central carrier is genuinely greatest among ordinary two-connected regions. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem twoConnected_region_reachable_avoiding [Fintype V]
    (G : SimpleGraph V) (T : Set V) [Fintype T]
    (hT : TwoConnected (G.induce T)) (z : V) (a b : T)
    (haz : a.1 ≠ z) (hbz : b.1 ≠ z) :
    (G.induce {v | v ≠ z}).Reachable ⟨a.1, haz⟩ ⟨b.1, hbz⟩ := by
  classical
  by_cases hzT : z ∈ T
  · let zr : T := ⟨z, hzT⟩
    have haz' : a ≠ zr := fun he => haz (congrArg Subtype.val he)
    have hbz' : b ≠ zr := fun he => hbz (congrArg Subtype.val he)
    let f : (G.induce T).induce {v : T | v ≠ zr} →g G.induce {v | v ≠ z} :=
      { toFun := fun v => ⟨v.1.1, fun he => v.2 (Subtype.ext he)⟩
        map_rel' := fun e => e }
    exact ((hT.2.2 zr) ⟨a, haz'⟩ ⟨b, hbz'⟩).map f
  · let f : G.induce T →g G.induce {v | v ≠ z} :=
      { toFun := fun v => ⟨v.1, fun he => hzT
          (Eq.mp (congrArg (fun v : V => v ∈ T) he) v.2)⟩
        map_rel' := fun e => e }
    exact (hT.2.1 a b).map f

theorem carrier_twoConnected_region_subset [Fintype V] (G : SimpleGraph V)
    (S : Set V) (hS : SingleAttachmentCarrier G S) (w y : V)
    (hw : w ∈ S) (hy : y ∈ S) (hwy : w ≠ y)
    (T : Set V) [Fintype T] (hT : TwoConnected (G.induce T))
    (hwT : w ∈ T) (hyT : y ∈ T) : T ⊆ S := by
  classical
  intro v hvT
  by_contra hvS
  let C := (G.induce Sᶜ).connectedComponentMk ⟨v, hvS⟩
  let vr : C.supp := ⟨⟨v, hvS⟩, rfl⟩
  let a := carrierAttachment G S hS C
  have hva : v ≠ a.1 := fun he => hvS
    (Eq.mpr (congrArg (fun v : V => v ∈ S) he) a.2)
  have hescape : ∀ (u : V), u ∈ T → u ∈ S → u ≠ a.1 → False := by
    intro u huT huS hua
    have hr := twoConnected_region_reachable_avoiding G T hT a.1 ⟨v, hvT⟩ ⟨u, huT⟩ hva hua
    obtain ⟨p⟩ := hr
    let R : Set V := {a.1}
    have hRS : R ⊆ S := by
      intro z hz
      change z = a.1 at hz
      exact Eq.mpr (congrArg (fun z : V => z ∈ S) hz) a.2
    have huC := carrier_old_component_walk_stays G S R hS hRS C (show a.1 ∈ R from rfl) p
      (show v ∈ componentRegion C Set.univ from ⟨vr, Set.mem_univ vr, rfl⟩)
    exact Set.disjoint_left.mp (componentRegion_disjoint C Set.univ) huC huS
  by_cases haw : a.1 = w
  · exact hescape y hyT hy (fun he => hwy (haw.symm.trans he.symm))
  · exact hescape w hwT hw (fun he => haw he.symm)

theorem central_greatest_carrier_exists [Fintype V] (G : SimpleGraph V)
    (w y : V) (hwy : w ≠ y) (hG : G.Connected) (hV : 3 ≤ Fintype.card V)
    (hGw : (G.induce {v | v ≠ w}).Connected)
    (hGy : (G.induce {v | v ≠ y}).Connected)
    (hpair : ∀ (z : V) (hwz : w ≠ z) (hyz : y ≠ z),
      (G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩ =
        (G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩) :
    ∃ S : Set V, RootCarrier G w y S ∧
      ∃ iS : Fintype S, @TwoConnected S iS (G.induce S) ∧
        ∀ (T : Set V) (iT : Fintype T), w ∈ T → y ∈ T →
          @TwoConnected T iT (G.induce T) → T ⊆ S := by
  classical
  obtain ⟨S, hS, iS, hTwo⟩ := central_twoConnected_carrier_exists G w y hwy hG hV hGw hGy hpair
  refine ⟨S, hS, iS, hTwo, ?_⟩
  intro T iT hwT hyT hT
  exact @carrier_twoConnected_region_subset V _ G S hS.2.2 w y hS.1 hS.2.1 hwy T iT hT hwT hyT

#print axioms twoConnected_region_reachable_avoiding
#print axioms carrier_twoConnected_region_subset
#print axioms central_greatest_carrier_exists
end TaskH.Gao
