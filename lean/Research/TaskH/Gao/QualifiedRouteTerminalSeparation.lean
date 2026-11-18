import Research.TaskH.Gao.QualifiedRouteAnchorCrossing
import Research.TaskH.Gao.TerminalFragmentCarrierRoute

/-! A real terminal separator confines every ordinary two-connected carrier
meeting its interior. Maximality gives equality, not an assumed block cover. -/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem twoConnected_carrier_meeting_terminal_subset (G : SimpleGraph V)
    (I : Set V) (b : V) (hI : TerminalFragment G I b)
    (S : Set V) [Fintype S] (hS : TwoConnected (G.induce S))
    (r : V) (hrS : r ∈ S) (hrI : r ∈ I) : S ⊆ fragmentBlock I b := by
  classical
  have hrb : r ≠ b := fun he => hI.2.1
    (Eq.mp (congrArg (fun r : V => r ∈ I) he) hrI)
  intro t htS
  by_cases htb : t = b
  · exact Or.inl htb
  · have hconn : (G.induce (S \ {b})).Connected := by
      by_cases hbS : b ∈ S
      · let br : S := ⟨b, hbS⟩
        exact (carrierDeleteGraphIso G S br).connected_iff.mp (hS.2.2 br)
      · let f : G.induce S →g G.induce (S \ {b}) :=
          { toFun := fun v => ⟨v.1, v.2, fun he => hbS
              (Eq.mp (congrArg (fun z : V => z ∈ S) he) v.2)⟩
            map_rel' := fun e => e }
        have hf : Function.Surjective f := fun v => ⟨⟨v.1, v.2.1⟩, Subtype.ext rfl⟩
        exact Connected.map f hf hS.2.1
    let rr : (S \ {b} : Set V) := ⟨r, hrS, hrb⟩
    let tr : (S \ {b} : Set V) := ⟨t, htS, htb⟩
    let J : Set (S \ {b} : Set V) := {v | v.1 ∈ I}
    have hc : ∀ a ∈ J, ∀ d, (G.induce (S \ {b})).Adj a d → d ∈ J := by
      intro a ha d ead
      rcases hI.2.2.1 a.1 ha d.1 ead with he | hdI
      · exact False.elim (d.2.2 he)
      · exact hdI
    obtain ⟨p⟩ := hconn rr tr
    exact Or.inr (terminal_walk_endpoint_mem_of_closed (G.induce (S \ {b})) J hc p hrI)

theorem maximal_carrier_terminal_equality_or_disjoint [Fintype V]
    (G : SimpleGraph V) (I : Set V) (b : V) (hI : TerminalFragment G I b)
    (S : Set V) [Fintype S] (hS : TwoConnected (G.induce S))
    (hmax : ∀ (T : Set V) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (G.induce T) → T ⊆ S) :
    S = fragmentBlock I b ∨ Disjoint I S := by
  classical
  by_cases he : S = fragmentBlock I b
  · exact Or.inl he
  · right
    apply Set.disjoint_left.mpr
    intro r hrI hrS
    have hsub := twoConnected_carrier_meeting_terminal_subset G I b hI S hS r hrS hrI
    have hcardS : 3 ≤ S.ncard := by
      simpa only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq] using hS.1
    have hcardB := hcardS.trans (Set.ncard_le_ncard hsub)
    rw [fragmentBlock_ncard I b hI.2.1] at hcardB
    have hcardI : 2 ≤ I.ncard := by omega
    let : Fintype (fragmentBlock I b) := Fintype.ofFinite _
    have hB := terminalFragment_twoConnected G I b hI hcardI
    have hrev := hmax (fragmentBlock I b) inferInstance hsub hB
    exact he (Set.Subset.antisymm hsub hrev)

theorem maximal_carrier_containing_terminal_point [Fintype V]
    (G : SimpleGraph V) (I : Set V) (b y : V) (hI : TerminalFragment G I b)
    (hyI : y ∈ I) (S : Set V) [Fintype S] (hS : TwoConnected (G.induce S))
    (hmax : ∀ (T : Set V) (iT : Fintype T), S ⊆ T →
      @TwoConnected T iT (G.induce T) → T ⊆ S) (hyS : y ∈ S) :
    S = fragmentBlock I b := by
  rcases maximal_carrier_terminal_equality_or_disjoint G I b hI S hS hmax with he | hd
  · exact he
  · exact False.elim (Set.disjoint_left.mp hd hyI hyS)

#print axioms twoConnected_carrier_meeting_terminal_subset
#print axioms maximal_carrier_terminal_equality_or_disjoint
#print axioms maximal_carrier_containing_terminal_point
end TaskH.Gao
