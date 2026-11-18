import Research.TaskH.Gao.MaximalRegionActualAttachments
import Research.TaskH.Gao.CarrierPeeling

/-! Actual simple-path double crossing distinguishes the two true core anchors.
It does not accept the off-chain every-path-passes-one-cut predicate. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem carrier_anchor_on_walk_to_core (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (a b : V) (hb : b ∈ S)
    (p : G.Walk a b) : (carrierAnchor G S hS a).1 ∈ p.support := by
  classical
  by_cases ha : a ∈ S
  · rw [carrierAnchor_mem G S hS a ha]
    exact p.start_mem_support
  · let E := (G.induce Sᶜ).connectedComponentMk ⟨a, ha⟩
    let ar : E.supp := ⟨⟨a, ha⟩, rfl⟩
    rw [carrierAnchor_outside G S hS a ha]
    by_contra hn
    let c := carrierAttachment G S hS E
    have hs : ∀ z ∈ p.support, z ∈ ({c.1} : Set V)ᶜ := by
      intro z hz he
      have he' : z = c.1 := he
      exact hn (Eq.mp (congrArg (fun z : V => z ∈ p.support) he') hz)
    let q := p.induce ({c.1} : Set V)ᶜ hs
    have hstay := carrier_old_component_walk_stays G S {c.1} hS
      (show ({c.1} : Set V) ⊆ S from by
        intro z hz
        have he : z = c.1 := hz
        exact Eq.mpr (congrArg (fun z : V => z ∈ S) he) c.2)
      E (show (carrierAttachment G S hS E).1 ∈ ({c.1} : Set V) from rfl)
      q (show a ∈ componentRegion E Set.univ from ⟨ar, Set.mem_univ ar, rfl⟩)
    exact Set.disjoint_left.mp (componentRegion_disjoint E Set.univ) hstay hb

theorem simple_path_two_core_points_distinct_anchors (G : SimpleGraph V)
    (S : Set V) (hS : SingleAttachmentCarrier G S) (a b : V)
    (p : G.Walk a b) (hp : p.IsPath)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hup : u ∈ p.support) (hvp : v ∈ p.support) :
    carrierAnchor G S hS a ≠ carrierAnchor G S hS b := by
  classical
  intro hab
  have hall : ∀ w ∈ S, w ∈ p.support → w = (carrierAnchor G S hS a).1 := by
    intro w hw hwp
    by_contra hwa
    let q := p.takeUntil w hwp
    let r := p.dropUntil w hwp
    have hsplit : (q.append r).IsPath := by
      change ((p.takeUntil w hwp).append (p.dropUntil w hwp)).IsPath
      rw [Walk.take_spec]
      exact hp
    have haq := carrier_anchor_on_walk_to_core G S hS a w hw q
    have hbr := carrier_anchor_on_walk_to_core G S hS b w hw r.reverse
    have har : (carrierAnchor G S hS a).1 ∈ r.support := by
      have hbr' : (carrierAnchor G S hS b).1 ∈ r.support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hbr
      exact Eq.mpr (congrArg (fun z : V => z ∈ r.support) (congrArg Subtype.val hab)) hbr'
    exact (hsplit.ne_of_mem_support_of_append (fun he => hwa he.symm) haq har) rfl
  exact huv ((hall u hu hup).trans (hall v hv hvp).symm)

theorem connected_set_in_actual_outside_component (G : SimpleGraph V)
    (S I : Set V) (hI : (G.induce I).Connected) (hIS : Disjoint I S) :
    ∃ E : (G.induce Sᶜ).ConnectedComponent, I ⊆ componentRegion E Set.univ := by
  classical
  obtain ⟨r⟩ := hI.nonempty
  have hrS : r.1 ∉ S := fun hr => Set.disjoint_left.mp hIS r.2 hr
  let E := (G.induce Sᶜ).connectedComponentMk ⟨r.1, hrS⟩
  let f : G.induce I →g G.induce Sᶜ :=
    { toFun := fun z => ⟨z.1, fun hz => Set.disjoint_left.mp hIS z.2 hz⟩
      map_rel' := fun e => e }
  refine ⟨E, ?_⟩
  intro z hz
  have hzr := (hI r ⟨z, hz⟩).map f
  have he := ConnectedComponent.sound hzr
  let zr : E.supp := ⟨f ⟨z, hz⟩, he.symm⟩
  exact ⟨zr, Set.mem_univ zr, rfl⟩

#print axioms carrier_anchor_on_walk_to_core
#print axioms simple_path_two_core_points_distinct_anchors
#print axioms connected_set_in_actual_outside_component
end TaskH.Gao
