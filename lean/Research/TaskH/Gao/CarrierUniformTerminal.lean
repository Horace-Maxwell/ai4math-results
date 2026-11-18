import Research.TaskH.Gao.CarrierAvoidingSpokes

/-!
Uniform attachment forces an actual terminal fragment, including every
original-graph deletion clause. Hence two terminal-free roots force two
different genuine attachment directions of the internally selected carrier.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u}

theorem carrier_uniform_root_closed (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (b : V)
    (hU : ∀ C, (carrierAttachment G S hS C).1 = b) :
    ∀ a ∈ S, a ≠ b → ∀ d, G.Adj a d → d ∈ S := by
  classical
  intro a haS hab d ead
  by_contra hdS
  let C := (G.induce Sᶜ).connectedComponentMk ⟨d, hdS⟩
  let dr : C.supp := ⟨⟨d, hdS⟩, rfl⟩
  have he : a = (carrierAttachment G S hS C).1 :=
    congrArg Subtype.val (carrierAttachment_unique G S hS C dr ⟨a, haS⟩ ead.symm)
  exact hab (he.trans (hU C))

theorem carrier_uniform_terminalFragment [Fintype V] (G : SimpleGraph V)
    (S : Set V) [Fintype S] (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (hTwo : TwoConnected (G.induce S)) (b : V) (hbS : b ∈ S)
    (hU : ∀ C, (carrierAttachment G S hS C).1 = b) :
    TerminalFragment G (S \ {b}) b := by
  classical
  let I := S \ {b}
  let br : S := ⟨b, hbS⟩
  obtain ⟨d, hdb⟩ := Fintype.exists_ne_of_one_lt_card
    (by have hh := hTwo.1; omega : 1 < Fintype.card S) br
  have hIne : I.Nonempty := ⟨d.1, d.2, fun he => hdb (Subtype.ext he)⟩
  have hbI : b ∉ I := fun h => h.2 rfl
  have hclosedS := carrier_uniform_root_closed G S hS b hU
  have hclosedI : ∀ a ∈ I, ∀ d, G.Adj a d → d = b ∨ d ∈ I := by
    intro a ha d ead
    have hdS := hclosedS a ha.1 ha.2 d ead
    by_cases hdb : d = b
    · exact Or.inl hdb
    · exact Or.inr ⟨hdS, hdb⟩
  have hIconn : (G.induce I).Connected :=
    (carrierDeleteGraphIso G S br).connected_iff.mp (hTwo.2.2 br)
  have hComp : (G.induce {v | v ∉ I}).Connected :=
    fragment_complement_connected G I b hbI hclosedI hG
  have hBeq : fragmentBlock I b = S := by
    ext v
    change (v = b ∨ (v ∈ S ∧ v ≠ b)) ↔ v ∈ S
    constructor
    · rintro (he | hv)
      · exact Eq.mpr (congrArg (fun v : V => v ∈ S) he) hbS
      · exact hv.1
    · intro hv
      by_cases he : v = b
      · exact Or.inl he
      · exact Or.inr ⟨hv, he⟩
  refine ⟨hIne, hbI, hclosedI, hIconn, hComp, ?_, ?_, ?_⟩
  · rw [hBeq]
    exact hTwo.2.1
  · intro c hcI
    let cr : S := ⟨c, hcI.1⟩
    have hflat : (G.induce (S \ {c})).Connected :=
      (carrierDeleteGraphIso G S cr).connected_iff.mp (hTwo.2.2 cr)
    have hall : ∀ C, (carrierAttachment G S hS C).1 ≠ c := by
      intro C he
      exact hcI.2 (he.symm.trans (hU C))
    exact carrier_global_deleted_connected G S hS c hcI.1
      ⟨b, hbS, fun he => hcI.2 he.symm⟩ hall hflat
  · rw [hBeq]
    exact hTwo.2.2

theorem carrier_two_distinct_attachment_vertices [Fintype V] (G : SimpleGraph V)
    (S : Set V) [Fintype S] (hS : SingleAttachmentCarrier G S)
    (hG : G.Connected) (hTwo : TwoConnected (G.induce S))
    (w y : V) (hw : w ∈ S) (hy : y ∈ S) (hwy : w ≠ y)
    (hwavoid : ∀ I b, TerminalFragment G I b → w ∉ I)
    (hyavoid : ∀ I b, TerminalFragment G I b → y ∉ I) :
    ∃ C D : (G.induce Sᶜ).ConnectedComponent,
      (carrierAttachment G S hS C).1 ≠ (carrierAttachment G S hS D).1 := by
  classical
  by_contra hn
  have hSame : ∀ C D, (carrierAttachment G S hS C).1 = (carrierAttachment G S hS D).1 := by
    intro C D
    by_contra hne
    exact hn ⟨C, D, hne⟩
  by_cases hex : ∃ C, (carrierAttachment G S hS C).1 ≠ w
  · obtain ⟨C, hCw⟩ := hex
    let b := (carrierAttachment G S hS C).1
    have hU : ∀ D, (carrierAttachment G S hS D).1 = b := fun D => hSame D C
    have hT := carrier_uniform_terminalFragment G S hS hG hTwo b
      (carrierAttachment G S hS C).2 hU
    exact hwavoid (S \ {b}) b hT ⟨hw, fun he => hCw he.symm⟩
  · have hU : ∀ C, (carrierAttachment G S hS C).1 = w := by
      intro C
      by_contra hne
      exact hex ⟨C, hne⟩
    have hT := carrier_uniform_terminalFragment G S hS hG hTwo w hw hU
    exact hyavoid (S \ {w}) w hT ⟨hy, hwy.symm⟩

theorem central_greatest_dual_attachment_carrier_exists [Fintype V]
    (G : SimpleGraph V) (w y : V) (hwy : w ≠ y)
    (hG : G.Connected) (hV : 3 ≤ Fintype.card V)
    (hGw : (G.induce {v | v ≠ w}).Connected)
    (hGy : (G.induce {v | v ≠ y}).Connected)
    (hpair : ∀ (z : V) (hwz : w ≠ z) (hyz : y ≠ z),
      (G.induce {v | v ≠ z}).connectedComponentMk ⟨w, hwz⟩ =
        (G.induce {v | v ≠ z}).connectedComponentMk ⟨y, hyz⟩)
    (hwavoid : ∀ I b, TerminalFragment G I b → w ∉ I)
    (hyavoid : ∀ I b, TerminalFragment G I b → y ∉ I) :
    ∃ (S : Set V) (hS : RootCarrier G w y S),
      ∃ iS : Fintype S, @TwoConnected S iS (G.induce S) ∧
        (∀ (T : Set V) (iT : Fintype T), w ∈ T → y ∈ T →
          @TwoConnected T iT (G.induce T) → T ⊆ S) ∧
        ∃ C D : (G.induce Sᶜ).ConnectedComponent,
          (carrierAttachment G S hS.2.2 C).1 ≠ (carrierAttachment G S hS.2.2 D).1 := by
  classical
  obtain ⟨S, hS, iS, hTwo, hGreat⟩ := central_greatest_carrier_exists G w y hwy hG hV hGw hGy hpair
  refine ⟨S, hS, iS, hTwo, hGreat, ?_⟩
  exact @carrier_two_distinct_attachment_vertices V _ G S iS hS.2.2 hG hTwo
    w y hS.1 hS.2.1 hwy hwavoid hyavoid

#print axioms carrier_uniform_root_closed
#print axioms carrier_uniform_terminalFragment
#print axioms carrier_two_distinct_attachment_vertices
#print axioms central_greatest_dual_attachment_carrier_exists
end TaskH.Gao
