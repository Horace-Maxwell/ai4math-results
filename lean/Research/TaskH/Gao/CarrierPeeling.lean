import Research.TaskH.Gao.CarrierDeletedConnectivity

/-!
Actual outside components are stable under carrier shrinkage whenever their
unique attachment remains. This proves the strict peel boundary property
without taking a partition or coverage statement as an oracle.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

theorem carrier_component_boundary_nonempty (G : SimpleGraph V) (S : Set V)
    (hG : G.Connected) (hS : S.Nonempty) (C : (G.induce Sᶜ).ConnectedComponent) :
    ∃ (a : S) (v : C.supp), G.Adj a.1 (componentVertex C v) := by
  classical
  by_contra hn
  let E := componentRegion C Set.univ
  have hclosed : ∀ a ∈ E, ∀ d, G.Adj a d → d ∈ E := by
    rintro a ⟨ar, _har, he⟩ d ead
    have evd : G.Adj (componentVertex C ar) d :=
      Eq.mpr (congrArg (fun a : V => G.Adj a d) he) ead
    by_cases hd : d ∈ S
    · exact False.elim (hn ⟨⟨d, hd⟩, ar, evd.symm⟩)
    · let dr : C.supp := ⟨⟨d, hd⟩, C.mem_supp_of_adj_mem_supp ar.2 evd⟩
      exact ⟨dr, Set.mem_univ dr, rfl⟩
  have hwalk : ∀ {a d : V} (p : G.Walk a d), a ∈ E → d ∈ E := by
    intro a d p
    induction p with
    | nil => intro ha; exact ha
    | @cons a b d e p ih => intro ha; exact ih (hclosed a ha b e)
  obtain ⟨a, ha⟩ := hS
  obtain ⟨v, hv⟩ := C.nonempty_supp
  let vr : C.supp := ⟨v, hv⟩
  obtain ⟨p⟩ := hG (componentVertex C vr) a
  have haE := hwalk p (show componentVertex C vr ∈ E from ⟨vr, Set.mem_univ vr, rfl⟩)
  exact Set.disjoint_left.mp (componentRegion_disjoint C Set.univ) haE ha

theorem carrier_old_component_walk_stays (G : SimpleGraph V) (S T : Set V)
    (hS : SingleAttachmentCarrier G S) (_hTS : T ⊆ S)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hAT : (carrierAttachment G S hS C).1 ∈ T)
    {a b : {v : V // v ∉ T}} (p : (G.induce Tᶜ).Walk a b)
    (ha : a.1 ∈ componentRegion C Set.univ) :
    b.1 ∈ componentRegion C Set.univ := by
  revert ha
  induction p with
  | nil => intro ha; exact ha
  | @cons a d b e p ih =>
    intro ha
    obtain ⟨ar, _har, he⟩ := ha
    have evd : G.Adj (componentVertex C ar) d.1 :=
      Eq.mpr (congrArg (fun a : V => G.Adj a d.1) he) e
    have hdS : d.1 ∉ S := by
      intro hdS
      have heq : (⟨d.1, hdS⟩ : S) = carrierAttachment G S hS C :=
        carrierAttachment_unique G S hS C ar ⟨d.1, hdS⟩ evd
      have heq' : d.1 = (carrierAttachment G S hS C).1 := congrArg Subtype.val heq
      exact d.2 (Eq.mpr (congrArg (fun v : V => v ∈ T) heq') hAT)
    let dr : C.supp := ⟨⟨d.1, hdS⟩, C.mem_supp_of_adj_mem_supp ar.2 evd⟩
    exact ih ⟨dr, Set.mem_univ dr, rfl⟩

theorem carrier_stable_component_boundary (G : SimpleGraph V) (S T : Set V)
    (hS : SingleAttachmentCarrier G S) (hTS : T ⊆ S)
    (C : (G.induce Sᶜ).ConnectedComponent)
    (hAT : (carrierAttachment G S hS C).1 ∈ T)
    (D : (G.induce Tᶜ).ConnectedComponent)
    (v : C.supp) (hv : (⟨componentVertex C v,
      fun h => v.1.2 (hTS h)⟩ : {v : V // v ∉ T}) ∈ D.supp) :
    ∀ (w : D.supp) (z : T), G.Adj (componentVertex D w) z.1 →
      z.1 = (carrierAttachment G S hS C).1 := by
  intro w z ewz
  have hr : (G.induce Tᶜ).Reachable
      ⟨componentVertex C v, fun h => v.1.2 (hTS h)⟩ w.1 :=
    D.reachable_of_mem_supp hv w.2
  obtain ⟨p⟩ := hr
  have hwE := carrier_old_component_walk_stays G S T hS hTS C hAT p
    (show componentVertex C v ∈ componentRegion C Set.univ from ⟨v, Set.mem_univ v, rfl⟩)
  obtain ⟨wr, _hwr, he⟩ := hwE
  have ewr : G.Adj (componentVertex C wr) z.1 :=
    Eq.mpr (congrArg (fun v : V => G.Adj v z.1) he) ewz
  exact congrArg Subtype.val (carrierAttachment_unique G S hS C wr ⟨z.1, hTS z.2⟩ ewr)

theorem singleAttachmentCarrier_peel (G : SimpleGraph V) (S T : Set V)
    (hS : SingleAttachmentCarrier G S) (hG : G.Connected)
    (hTS : T ⊆ S) (c : V) (hc : c ∈ T)
    (hclosed : ∀ a ∈ T, a ≠ c → ∀ d ∈ S, G.Adj a d → d ∈ T) :
    SingleAttachmentCarrier G T := by
  classical
  intro D
  obtain ⟨a0, v0, e0⟩ := carrier_component_boundary_nonempty G T hG ⟨c, hc⟩ D
  by_cases hex : ∃ (v : D.supp) (z : T),
      G.Adj (componentVertex D v) z.1 ∧ z.1 ≠ c
  · obtain ⟨v, z, evz, hzc⟩ := hex
    have hvS : componentVertex D v ∉ S := by
      intro hvS
      exact v.1.2 (hclosed z.1 z.2 hzc (componentVertex D v) hvS evz.symm)
    let C := (G.induce Sᶜ).connectedComponentMk ⟨componentVertex D v, hvS⟩
    let vr : C.supp := ⟨⟨componentVertex D v, hvS⟩, rfl⟩
    have hzA : (⟨z.1, hTS z.2⟩ : S) = carrierAttachment G S hS C :=
      carrierAttachment_unique G S hS C vr ⟨z.1, hTS z.2⟩ evz
    have hzA' : z.1 = (carrierAttachment G S hS C).1 := congrArg Subtype.val hzA
    have hAT : (carrierAttachment G S hS C).1 ∈ T :=
      Eq.mp (congrArg (fun a : V => a ∈ T) hzA') z.2
    have hvD : (⟨componentVertex C vr,
        fun h => vr.1.2 (hTS h)⟩ : {v : V // v ∉ T}) ∈ D.supp := v.2
    refine ⟨z, ⟨v, evz.symm⟩, ?_⟩
    intro w t ewt
    apply Subtype.ext
    exact (carrier_stable_component_boundary G S T hS hTS C hAT D vr hvD w t ewt).trans hzA'.symm
  · have hall : ∀ (v : D.supp) (z : T), G.Adj (componentVertex D v) z.1 → z.1 = c := by
      intro v z evz
      by_contra hzc
      exact hex ⟨v, z, evz, hzc⟩
    let cr : T := ⟨c, hc⟩
    have ha0 : a0.1 = c := hall v0 a0 e0.symm
    refine ⟨cr, ⟨v0, ?_⟩, ?_⟩
    · exact Eq.mp (congrArg (fun a : V => G.Adj a (componentVertex D v0)) ha0) e0
    · intro v z evz
      exact Subtype.ext (hall v z evz)

theorem induced_subset_root_connected (G : SimpleGraph V) (S T : Set V)
    (hTS : T ⊆ S) (c : V) (hc : c ∈ T) (hG : (G.induce S).Connected)
    (hclosed : ∀ a ∈ T, a ≠ c → ∀ d ∈ S, G.Adj a d → d ∈ T) :
    (G.induce T).Connected := by
  let U : Set S := {v | v.1 ∈ T}
  let cr : S := ⟨c, hTS hc⟩
  have hU := TaskH.Fan.rootedSet_connected (G.induce S) U cr hc (by
    intro a ha hac d ead
    have hac' : a.1 ≠ c := fun he => hac (Subtype.ext he)
    exact hclosed a.1 ha hac' d.1 d.2 ead) hG
  let f : (G.induce S).induce U →g G.induce T :=
    { toFun := fun v => ⟨v.1.1, v.2⟩
      map_rel' := fun e => e }
  have hf : Function.Surjective f := by
    intro v
    exact ⟨⟨⟨v.1, hTS v.2⟩, v.2⟩, Subtype.ext rfl⟩
  exact hU.map f hf

#print axioms carrier_component_boundary_nonempty
#print axioms carrier_old_component_walk_stays
#print axioms carrier_stable_component_boundary
#print axioms singleAttachmentCarrier_peel
#print axioms induced_subset_root_connected
end TaskH.Gao
