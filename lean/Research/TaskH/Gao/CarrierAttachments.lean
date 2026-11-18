import Research.TaskH.Gao.ComponentFragmentTransport

/-!
A carrier predicate on actual outside components and their unique actual
attachment vertices. No block, coverage, path or child theorem is an input.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

def SingleAttachmentCarrier (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ C : (G.induce Sᶜ).ConnectedComponent, ∃ a : S,
    (∃ v : C.supp, G.Adj a.1 (componentVertex C v)) ∧
      ∀ (v : C.supp) (z : S), G.Adj (componentVertex C v) z.1 → z = a

noncomputable def carrierAttachment (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (C : (G.induce Sᶜ).ConnectedComponent) : S :=
  Classical.choose (hS C)

theorem carrierAttachment_spoke (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (C : (G.induce Sᶜ).ConnectedComponent) :
    ∃ v : C.supp, G.Adj (carrierAttachment G S hS C).1 (componentVertex C v) :=
  (Classical.choose_spec (hS C)).1

theorem carrierAttachment_unique (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (C : (G.induce Sᶜ).ConnectedComponent)
    (v : C.supp) (z : S) (e : G.Adj (componentVertex C v) z.1) :
    z = carrierAttachment G S hS C :=
  (Classical.choose_spec (hS C)).2 v z e

noncomputable def carrierAnchor (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) : V → S := by
  classical
  exact fun v => if hv : v ∈ S then ⟨v, hv⟩ else
    carrierAttachment G S hS ((G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩)

theorem carrierAnchor_mem (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (v : V) (hv : v ∈ S) :
    carrierAnchor G S hS v = ⟨v, hv⟩ := by
  classical
  simp only [carrierAnchor, dite_eq_left hv]

theorem carrierAnchor_outside (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (v : V) (hv : v ∉ S) :
    carrierAnchor G S hS v =
      carrierAttachment G S hS ((G.induce Sᶜ).connectedComponentMk ⟨v, hv⟩) := by
  classical
  simp only [carrierAnchor, dite_eq_right hv]

theorem carrierAnchor_edge_cases (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) {a b : V} (e : G.Adj a b) :
    carrierAnchor G S hS a = carrierAnchor G S hS b ∨ (a ∈ S ∧ b ∈ S) := by
  classical
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · exact Or.inr ⟨ha, hb⟩
    · left
      let C := (G.induce Sᶜ).connectedComponentMk ⟨b, hb⟩
      let br : C.supp := ⟨⟨b, hb⟩, rfl⟩
      rw [carrierAnchor_mem G S hS a ha, carrierAnchor_outside G S hS b hb]
      exact carrierAttachment_unique G S hS C br ⟨a, ha⟩ e.symm
  · by_cases hb : b ∈ S
    · left
      let C := (G.induce Sᶜ).connectedComponentMk ⟨a, ha⟩
      let ar : C.supp := ⟨⟨a, ha⟩, rfl⟩
      rw [carrierAnchor_outside G S hS a ha, carrierAnchor_mem G S hS b hb]
      exact (carrierAttachment_unique G S hS C ar ⟨b, hb⟩ e).symm
    · left
      rw [carrierAnchor_outside G S hS a ha, carrierAnchor_outside G S hS b hb]
      exact congrArg (carrierAttachment G S hS)
        (ConnectedComponent.connectedComponentMk_eq_of_adj
          (G := G.induce Sᶜ) (v := ⟨a, ha⟩) (w := ⟨b, hb⟩) e)

theorem carrierAnchor_adj_or_eq (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) {a b : V} (e : G.Adj a b) :
    carrierAnchor G S hS a = carrierAnchor G S hS b ∨
      (G.induce S).Adj (carrierAnchor G S hS a) (carrierAnchor G S hS b) := by
  rcases carrierAnchor_edge_cases G S hS e with he | ⟨ha, hb⟩
  · exact Or.inl he
  · right
    rw [carrierAnchor_mem G S hS a ha, carrierAnchor_mem G S hS b hb]
    exact e

theorem carrierAnchor_surjective (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) : Function.Surjective (carrierAnchor G S hS) := by
  intro v
  exact ⟨v.1, carrierAnchor_mem G S hS v.1 v.2⟩

theorem singleAttachmentCarrier_connected (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (hG : G.Connected) :
    (G.induce S).Connected := by
  exact TaskH.Fan.connected_of_surjective_adj_or_eq (carrierAnchor G S hS)
    (carrierAnchor_surjective G S hS) (carrierAnchor_adj_or_eq G S hS) hG

theorem singleAttachmentCarrier_univ (G : SimpleGraph V) :
    SingleAttachmentCarrier G Set.univ := by
  intro C
  obtain ⟨v, hv⟩ := C.nonempty_supp
  exact False.elim (v.2 (Set.mem_univ v.1))

#print axioms SingleAttachmentCarrier
#print axioms carrierAttachment
#print axioms carrierAttachment_spoke
#print axioms carrierAttachment_unique
#print axioms carrierAnchor
#print axioms carrierAnchor_mem
#print axioms carrierAnchor_outside
#print axioms carrierAnchor_edge_cases
#print axioms carrierAnchor_adj_or_eq
#print axioms carrierAnchor_surjective
#print axioms singleAttachmentCarrier_connected
#print axioms singleAttachmentCarrier_univ
end TaskH.Gao
