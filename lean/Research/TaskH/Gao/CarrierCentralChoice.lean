import Research.TaskH.Gao.CarrierAttachmentCuts

/-! Finite minimum of actual carriers, strict real cutside peel, and actual central two-connectivity. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

def RootCarrier (G : SimpleGraph V) (w y : V) (S : Set V) : Prop :=
  w ∈ S ∧ y ∈ S ∧ SingleAttachmentCarrier G S

def carrierCutSide (G : SimpleGraph V) (S : Set V) (c : V)
    (C : (G.induce (S \ {c})).ConnectedComponent) : Set V :=
  {v | v = c ∨ ∃ u : C.supp, u.1.1 = v}

theorem rootCarrier_minimum_exists [Fintype V] (G : SimpleGraph V) (w y : V) :
    ∃ S : Set V, RootCarrier G w y S ∧
      ∀ T : Set V, RootCarrier G w y T → S.ncard ≤ T.ncard := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Set V, RootCarrier G w y S ∧ S.ncard = n
  have hex : ∃ n, P n := ⟨(Set.univ : Set V).ncard, Set.univ,
    ⟨Set.mem_univ w, Set.mem_univ y, singleAttachmentCarrier_univ G⟩, rfl⟩
  obtain ⟨S, hS, hcard⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  exact hcard.le.trans (Nat.find_min' hex ⟨T, hT, rfl⟩)

theorem carrierCutSide_subset (G : SimpleGraph V) (S : Set V) (c : V) (hc : c ∈ S)
    (C : (G.induce (S \ {c})).ConnectedComponent) : carrierCutSide G S c C ⊆ S := by
  rintro v (he | ⟨u, hu⟩)
  · exact Eq.mpr (congrArg (fun v : V => v ∈ S) he) hc
  · exact Eq.mp (congrArg (fun v : V => v ∈ S) hu) u.1.2.1

theorem carrierCutSide_closed (G : SimpleGraph V) (S : Set V) (c : V)
    (C : (G.induce (S \ {c})).ConnectedComponent) :
    ∀ a ∈ carrierCutSide G S c C, a ≠ c → ∀ d ∈ S, G.Adj a d →
      d ∈ carrierCutSide G S c C := by
  rintro a (he | ⟨u, hu⟩) hac d hdS ead
  · exact False.elim (hac he)
  · by_cases hdc : d = c
    · exact Or.inl hdc
    · have eud : G.Adj u.1.1 d :=
        Eq.mpr (congrArg (fun a : V => G.Adj a d) hu) ead
      let dr : C.supp := ⟨⟨d, hdS, hdc⟩, C.mem_supp_of_adj_mem_supp u.2 eud⟩
      exact Or.inr ⟨dr, rfl⟩

theorem carrierCutSide_strict [Fintype V] (G : SimpleGraph V) (S : Set V)
    (c : V) (hc : c ∈ S) (C : (G.induce (S \ {c})).ConnectedComponent)
    (r : ↥(S \ {c} : Set V)) (_hr : r ∈ C.supp)
    (hbad : ¬(G.induce (S \ {c})).Connected) :
    (carrierCutSide G S c C).ncard < S.ncard := by
  classical
  have hv : ∃ v : ↥(S \ {c} : Set V), v ∉ C.supp := by
    by_contra h
    apply hbad
    refine { preconnected := ?_, nonempty := ⟨r⟩ }
    intro a b
    have ha : a ∈ C.supp := by by_contra ha; exact h ⟨a, ha⟩
    have hb : b ∈ C.supp := by by_contra hb; exact h ⟨b, hb⟩
    exact C.reachable_of_mem_supp ha hb
  obtain ⟨v, hvC⟩ := hv
  apply Set.ncard_lt_ncard (s := carrierCutSide G S c C) (t := S) _ (Set.toFinite S)
  refine ⟨carrierCutSide_subset G S c hc C, ?_⟩
  intro hrev
  rcases hrev v.2.1 with he | ⟨u, hu⟩
  · exact v.2.2 he
  · have huv : u.1 = v := Subtype.ext hu
    exact hvC (Eq.mp (congrArg (fun a : ↥(S \ {c} : Set V) => a ∈ C.supp) huv) u.2)

theorem central_twoConnected_carrier_exists [Fintype V] (G : SimpleGraph V)
    (w y : V) (hwy : w ≠ y) (hG : G.Connected) (hV : 3 ≤ Fintype.card V)
    (hGw : (G.induce {v | v ≠ w}).Connected)
    (hGy : (G.induce {v | v ≠ y}).Connected)
    (hpair : ∀ (z : V) (hwz : w ≠ z) (hyz : y ≠ z),
      (G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩ =
        (G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩) :
    ∃ S : Set V, RootCarrier G w y S ∧
      ∃ iS : Fintype S, @TwoConnected S iS (G.induce S) := by
  classical
  obtain ⟨S, hS, hmin⟩ := rootCarrier_minimum_exists G w y
  let iS : Fintype S := Fintype.ofFinite _
  have horder := singleAttachmentCarrier_order_three G S hS.2.2 w y hS.1 hS.2.1 hwy hV hGw hGy
  have hcard : 3 ≤ @Fintype.card S iS := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq] using horder
  have hconn := singleAttachmentCarrier_connected G S hS.2.2 hG
  refine ⟨S, hS, iS, hcard, hconn, ?_⟩
  intro cr
  have hflat : (G.induce (S \ {cr.1})).Connected := by
    by_cases hcw : cr.1 = w
    · have hyc : y ≠ cr.1 := fun he => hwy (hcw.symm.trans he.symm)
      apply carrier_deleted_connected G S hS.2.2 cr.1 ⟨y, hS.2.1, hyc⟩
      rw [hcw]
      exact hGw
    · by_cases hcy : cr.1 = y
      · have hwc : w ≠ cr.1 := fun he => hwy (he.trans hcy)
        apply carrier_deleted_connected G S hS.2.2 cr.1 ⟨w, hS.1, hwc⟩
        rw [hcy]
        exact hGy
      · by_contra hbad
        have hwc : w ≠ cr.1 := fun he => hcw he.symm
        have hyc : y ≠ cr.1 := fun he => hcy he.symm
        let wr : ↥(S \ {cr.1} : Set V) := ⟨w, hS.1, hwc⟩
        let yr : ↥(S \ {cr.1} : Set V) := ⟨y, hS.2.1, hyc⟩
        let C := (G.induce (S \ {cr.1})).connectedComponentMk wr
        have hr : (G.induce (S \ {cr.1})).Reachable wr yr :=
          carrier_deleted_reachable G S hS.2.2 cr.1 wr yr
            (ConnectedComponent.exact (hpair cr.1 hwc hyc))
        have hyr : yr ∈ C.supp := (ConnectedComponent.sound hr).symm
        let T := carrierCutSide G S cr.1 C
        have hTS : T ⊆ S := carrierCutSide_subset G S cr.1 cr.2 C
        have hcT : cr.1 ∈ T := Or.inl rfl
        have hclosed := carrierCutSide_closed G S cr.1 C
        have hwT : w ∈ T := Or.inr ⟨⟨wr, rfl⟩, rfl⟩
        have hyT : y ∈ T := Or.inr ⟨⟨yr, hyr⟩, rfl⟩
        have hT : RootCarrier G w y T := ⟨hwT, hyT,
          singleAttachmentCarrier_peel G S T hS.2.2 hG hTS cr.1 hcT hclosed⟩
        have hlt : T.ncard < S.ncard := carrierCutSide_strict G S cr.1 cr.2 C wr rfl hbad
        exact (not_lt_of_ge (hmin T hT)) hlt
  exact (carrierDeleteGraphIso G S cr).connected_iff.mpr hflat

#print axioms RootCarrier
#print axioms carrierCutSide
#print axioms rootCarrier_minimum_exists
#print axioms carrierCutSide_subset
#print axioms carrierCutSide_closed
#print axioms carrierCutSide_strict
#print axioms central_twoConnected_carrier_exists
end TaskH.Gao
