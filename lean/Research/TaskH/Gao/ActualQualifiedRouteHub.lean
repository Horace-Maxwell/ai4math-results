import Research.TaskH.Gao.QualifiedRouteTerminalSeparation
import Research.TaskH.Gao.CarrierAttachmentCuts

/-! Intrinsic corrected on-chain qualification. A genuine simple path must
visit TWO DIFFERENT core vertices; passing one off-chain cut is insufficient. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def ActualQualifiedRouteHub (G : SimpleGraph V) (I : Set V) (b y : V)
    (S : Set V) : Prop :=
  (∃ iS : Fintype S, @TwoConnected S iS (G.induce S)) ∧
    (∀ (T : Set V) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (G.induce T) → T ⊆ S) ∧
    S ≠ fragmentBlock I b ∧
    (S ∩ {z | ¬(G.induce {w | w ≠ z}).Connected}).ncard ≤ 2 ∧
    ∃ r ∈ I, ∃ p : G.Walk r y, p.IsPath ∧
      ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ u ∈ p.support ∧ v ∈ p.support

theorem actual_qualified_route_side_data [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (I : Set V) (b : V) (hI : TerminalFragment G I b)
    (Y : Set V) (bt y : V) (hY : TerminalFragment G Y bt) (hyY : y ∈ Y)
    (S : Set V) [Fintype S] (hS : TwoConnected (G.induce S))
    (hmax : ∀ (T : Set V) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (G.induce T) → T ⊆ S)
    (hne : S ≠ fragmentBlock I b)
    (hcap : (S ∩ {z | ¬(G.induce {w | w ≠ z}).Connected}).ncard ≤ 2)
    (hroute : ∃ r ∈ I, ∃ p : G.Walk r y, p.IsPath ∧
      ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ u ∈ p.support ∧ v ∈ p.support) :
    ∃ u v : S, u ≠ v ∧
      (∀ z ∈ S, ¬(G.induce {w | w ≠ z}).Connected → z = u.1 ∨ z = v.1) ∧
      (y ∈ S → y = v.1) ∧
      ∃ E : (G.induce Sᶜ).ConnectedComponent,
        carrierAttachment G S (maximal_twoConnected_region_single_attachment G S hG hS hmax) E = u ∧
        I ⊆ componentRegion E Set.univ ∧
        (y = v.1 ∨ ∃ F : (G.induce Sᶜ).ConnectedComponent,
          carrierAttachment G S (maximal_twoConnected_region_single_attachment G S hG hS hmax) F = v ∧
          y ∈ componentRegion F Set.univ) := by
  classical
  have hIS : Disjoint I S :=
    (maximal_carrier_terminal_equality_or_disjoint G I b hI S hS hmax).resolve_left hne
  obtain ⟨E, hIE⟩ := connected_set_in_actual_outside_component G S I hI.2.2.2.1 hIS
  let hCar := maximal_twoConnected_region_single_attachment G S hG hS hmax
  let u := carrierAttachment G S hCar E
  let v := carrierAnchor G S hCar y
  obtain ⟨r, hrI, p, hp, c, hcS, d, hdS, hcd, hcp, hdp⟩ := hroute
  have hrS : r ∉ S := fun hh => Set.disjoint_left.mp hIS hrI hh
  have hrE : (⟨r, hrS⟩ : {z : V // z ∉ S}) ∈ E.supp := by
    obtain ⟨rr, _hrr, he⟩ := hIE hrI
    have he' : rr.1 = (⟨r, hrS⟩ : {z : V // z ∉ S}) := Subtype.ext he
    exact Eq.mp (congrArg (fun z : {z : V // z ∉ S} => z ∈ E.supp) he') rr.2
  have hru : carrierAnchor G S hCar r = u := by
    rw [carrierAnchor_outside G S hCar r hrS]
    exact congrArg (carrierAttachment G S hCar) hrE
  have hdistinct := simple_path_two_core_points_distinct_anchors G S hCar r y p hp
    c d hcS hdS hcd hcp hdp
  have huv : u ≠ v := fun he => hdistinct (hru.trans he)
  have huvval : u.1 ≠ v.1 := fun he => huv (Subtype.ext he)
  have huCut : ¬(G.induce {z | z ≠ u.1}).Connected :=
    carrierAttachment_cut G S hCar E v huv.symm
  by_cases hyS : y ∈ S
  · have hSB := maximal_carrier_containing_terminal_point G Y bt y hY hyY S hS hmax hyS
    have hvy : v.1 = y := congrArg Subtype.val (carrierAnchor_mem G S hCar y hyS)
    have hcutOnly : ∀ z ∈ S, ¬(G.induce {w | w ≠ z}).Connected → z = bt := by
      intro z hz hbad
      have hzB : z ∈ fragmentBlock Y bt := Eq.mp (congrArg (fun S : Set V => z ∈ S) hSB) hz
      rcases hzB with he | hzY
      · exact he
      · rcases hY with ⟨_hne, _hbt, _hclosed, _hYC, _hcomp, _hBC, hglobal, _hdel⟩
        exact False.elim (hbad (hglobal z hzY))
    have hubt := hcutOnly u.1 u.2 huCut
    refine ⟨u, v, huv, ?_, ?_, E, rfl, hIE, Or.inl hvy.symm⟩
    · intro z hz hbad
      exact Or.inl ((hcutOnly z hz hbad).trans hubt.symm)
    · intro _hy; exact hvy.symm
  · let F := (G.induce Sᶜ).connectedComponentMk ⟨y, hyS⟩
    have hFv : carrierAttachment G S hCar F = v :=
      (carrierAnchor_outside G S hCar y hyS).symm
    have huF : u ≠ carrierAttachment G S hCar F := fun he => huv (he.trans hFv)
    have hvCut : ¬(G.induce {z | z ≠ v.1}).Connected := by
      have hh := carrierAttachment_cut G S hCar F u huF
      exact Eq.mp (congrArg (fun z : S => ¬(G.induce {w | w ≠ z.1}).Connected) hFv) hh
    let K := S ∩ {z | ¬(G.induce {w | w ≠ z}).Connected}
    have hpair : ({u.1, v.1} : Set V) ⊆ K := by
      rintro z (he | he)
      · exact Eq.mpr (congrArg (fun z : V => z ∈ K) he) ⟨u.2, huCut⟩
      · exact Eq.mpr (congrArg (fun z : V => z ∈ K) he) ⟨v.2, hvCut⟩
    have hKeq : ({u.1, v.1} : Set V) = K :=
      Set.eq_of_subset_of_ncard_le hpair (by rw [Set.ncard_pair huvval]; exact hcap)
    let yr : F.supp := ⟨⟨y, hyS⟩, rfl⟩
    refine ⟨u, v, huv, ?_, ?_, E, rfl, hIE, Or.inr ⟨F, hFv, yr, Set.mem_univ yr, rfl⟩⟩
    · intro z hz hbad
      exact Eq.mpr (congrArg (fun K : Set V => z ∈ K) hKeq) ⟨hz, hbad⟩
    · intro hh; exact False.elim (hyS hh)

#print axioms ActualQualifiedRouteHub
#print axioms actual_qualified_route_side_data
end TaskH.Gao
