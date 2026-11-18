import Research.TaskH.Gao.NoHubOutsideActualCarrier
import Research.TaskH.Gao.NoHubOutsideActualLeafComponent
import Research.TaskH.Gao.CarrierCommonPointCutBound
import Research.TaskH.Gao.QualifiedRouteAnchorCrossing
import Research.TaskH.Gao.ActualQualifiedRouteHub

/-! The true outside components, two different attachment values, and a single
actual simple route are all constructed. No component-cover or linkage oracle. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem singleton_terminal_carrier_component_avoids_leaf
    (G : SimpleGraph V) (S : Set V) (y z : V)
    (hT : TerminalFragment G {y} z) (hzS : z ∈ S)
    (E : (G.induce Sᶜ).ConnectedComponent) (r : V)
    (hrE : r ∈ componentRegion E Set.univ) (hry : r ≠ y) :
    y ∉ componentRegion E Set.univ := by
  rintro ⟨ey, _hey, hey⟩
  obtain ⟨er, _her, her⟩ := hrE
  let f : E.toSimpleGraph →g G.induce {v | v ≠ z} :=
    { toFun := fun q => ⟨componentVertex E q, fun he => q.1.2
        (Eq.mpr (congrArg (fun v : V => v ∈ S) he) hzS)⟩
      map_rel' := fun e => e }
  obtain ⟨q⟩ := (E.connected_toSimpleGraph ey er).map f
  have hyStart : (f ey).1 ∈ ({y} : Set V) := hey
  have hrY := terminal_walk_stays_without_boundary G {y} z hT q hyStart
  have hrY' : r ∈ ({y} : Set V) :=
    Eq.mp (congrArg (fun v : V => v ∈ ({y} : Set V)) her) hrY
  exact hry hrY'

theorem singleton_terminal_common_carrier_attachment_ne_boundary [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected) (y p z : V)
    (hT : TerminalFragment G {y} z)
    (hcommon : ∀ (I : Set V) (b : V), TerminalFragment G I b → y ∉ I → p ∈ I)
    (S : Set V) [Fintype S] (hTwo : TwoConnected (G.induce S))
    (hCar : SingleAttachmentCarrier G S) (hzS : z ∈ S)
    (E : (G.induce Sᶜ).ConnectedComponent) (hpE : p ∈ componentRegion E Set.univ) :
    (carrierAttachment G S hCar E).1 ≠ z := by
  classical
  intro he
  have hyS : y ∉ S := singleton_terminal_outside_ordinary_carrier G y z hT S hTwo
  have hs2 : 1 < S.ncard := by
    have hs3 : 3 ≤ S.ncard := by simpa only [Set.fintypeCard_eq_ncard] using hTwo.1
    omega
  obtain ⟨t, htS, htz⟩ := Set.exists_ne_of_one_lt_ncard hs2 z
  have hty : t ≠ y := fun h => hyS (Eq.mp (congrArg (fun v : V => v ∈ S) h) htS)
  let D := (G.induce {v | v ≠ z}).connectedComponentMk ⟨t, htz⟩
  have hyD : y ∉ deletedInterior G z D :=
    singleton_terminal_deleted_component_avoids_leaf G y z t hT hty htz
  obtain ⟨hpz, hpD⟩ := terminal_common_point_in_deleted_component G y p z hG hcommon D hyD
  obtain ⟨q⟩ := ConnectedComponent.exact hpD
  have hsub : ({z} : Set V) ⊆ S := by
    intro a ha
    exact Eq.mpr (congrArg (fun a : V => a ∈ S) (show a = z from ha)) hzS
  have hAT : (carrierAttachment G S hCar E).1 ∈ ({z} : Set V) := he
  have htE := carrier_old_component_walk_stays G S {z} hCar hsub E hAT q hpE
  exact Set.disjoint_left.mp (componentRegion_disjoint E Set.univ) htE htS

theorem singleton_terminal_high_degree_qualified_hub [Fintype V]
    (G : SimpleGraph V) (hG : G.Connected)
    (I : Set V) (b : V) (hI : TerminalFragment G I b)
    (y p z : V) (hyI : y ∉ I) (hzB : z ∉ fragmentBlock I b)
    (hT : TerminalFragment G {y} z)
    (hcommon : ∀ (U : Set V) (d : V), TerminalFragment G U d → y ∉ U → p ∈ U)
    (hhigh : 3 ≤ (G.neighborSet z).ncard) :
    ∃ S : Set V, ActualQualifiedRouteHub G I b y S := by
  classical
  obtain ⟨S, iS, hzS, hTwo, hmax, hCar⟩ :=
    singleton_terminal_high_degree_actual_carrier G hG y p z hT hcommon hhigh
  let : Fintype S := iS
  have hyS : y ∉ S := singleton_terminal_outside_ordinary_carrier G y z hT S hTwo
  have hdis : Disjoint S I := terminal_twoConnected_region_avoids_interior
    G I b hI S hTwo z hzS hzB
  obtain ⟨E, hIE⟩ := connected_set_in_actual_outside_component G S I hI.2.2.2.1 hdis.symm
  have hpI : p ∈ I := hcommon I b hI hyI
  have hpE : p ∈ componentRegion E Set.univ := hIE hpI
  have hpy : p ≠ y := fun he => hyI (Eq.mp (congrArg (fun v : V => v ∈ I) he) hpI)
  have hyE : y ∉ componentRegion E Set.univ :=
    singleton_terminal_carrier_component_avoids_leaf G S y z hT hzS E p hpE hpy
  let Y := (G.induce Sᶜ).connectedComponentMk ⟨y, hyS⟩
  let yr : Y.supp := ⟨⟨y, hyS⟩, rfl⟩
  have hyY : y ∈ componentRegion Y Set.univ := ⟨yr, Set.mem_univ yr, rfl⟩
  have hYattach := (singleton_terminal_actual_leaf_component_attachment G hG y z hT S hCar hzS Y hyY).2
  have hcap := carrier_common_point_cut_ncard_le_two G S hCar hTwo hG y p hcommon E Y hpE hyY
  let a := carrierAttachment G S hCar E
  have haz : a.1 ≠ z := singleton_terminal_common_carrier_attachment_ne_boundary
    G hG y p z hT hcommon S hTwo hCar hzS E hpE
  have haY : a.1 ≠ (carrierAttachment G S hCar Y).1 := fun he => haz (he.trans hYattach)
  obtain ⟨r, hrI⟩ := hI.1
  have hrE : r ∈ componentRegion E Set.univ := hIE hrI
  have hrz : r ≠ z := fun he => hzB (Or.inr
    (Eq.mp (congrArg (fun v : V => v ∈ I) he) hrI))
  have hyz : y ≠ z := fun he => hT.2.1 (show z ∈ ({y} : Set V) from he.symm)
  obtain ⟨q, hq⟩ := hG.exists_isPath r y
  have haQ : a.1 ∈ q.support := by
    by_contra hn
    have hs : ∀ v ∈ q.support, v ∈ ({a.1} : Set V)ᶜ := by
      intro v hv he
      exact hn (Eq.mp (congrArg (fun v : V => v ∈ q.support) (show v = a.1 from he)) hv)
    let q' := q.induce ({a.1} : Set V)ᶜ hs
    have hsub : ({a.1} : Set V) ⊆ S := by
      intro v hv
      exact Eq.mpr (congrArg (fun v : V => v ∈ S) (show v = a.1 from hv)) a.2
    have hstay := carrier_old_component_walk_stays G S {a.1} hCar hsub E
      (show (carrierAttachment G S hCar E).1 ∈ ({a.1} : Set V) from rfl) q' hrE
    exact hyE hstay
  have hzQ : z ∈ q.support := by
    by_contra hn
    have hs : ∀ v ∈ q.reverse.support, v ≠ z := by
      intro v hv he
      have hv' : v ∈ q.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hv
      exact hn (Eq.mp (congrArg (fun v : V => v ∈ q.support) he) hv')
    let q' : (G.induce {v | v ≠ z}).Walk ⟨y, hyz⟩ ⟨r, hrz⟩ :=
      q.reverse.induce {v | v ≠ z} hs
    have hrY := terminal_walk_stays_without_boundary G {y} z hT q' (Set.mem_singleton y)
    exact hyI (Eq.mp (congrArg (fun v : V => v ∈ I) hrY) hrI)
  have hne : S ≠ fragmentBlock I b := fun he => hzB
    (Eq.mp (congrArg (fun T : Set V => z ∈ T) he) hzS)
  have hYQ : (carrierAttachment G S hCar Y).1 ∈ q.support :=
    Eq.mpr (congrArg (fun v : V => v ∈ q.support) hYattach) hzQ
  exact ⟨S, ⟨iS, hTwo⟩, hmax, hne, hcap, r, hrI, q, hq,
    a.1, a.2, (carrierAttachment G S hCar Y).1, (carrierAttachment G S hCar Y).2,
    haY, haQ, hYQ⟩

#print axioms singleton_terminal_carrier_component_avoids_leaf
#print axioms singleton_terminal_common_carrier_attachment_ne_boundary
#print axioms singleton_terminal_high_degree_qualified_hub
end TaskH.Gao
