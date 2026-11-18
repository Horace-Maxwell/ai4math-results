import Research.TaskH.Gao.CarrierAttachments

/-!
Actual component labels transport deletions and root-pair reachability into
an induced carrier. Detached branches labelled at the deleted attachment
use a real retained default point, without asserting global connectivity.
-/
set_option autoImplicit false
universe u
namespace TaskH.Gao
open SimpleGraph
variable {V : Type u}

noncomputable def carrierRetainedLabel (G : SimpleGraph V) (S : Set V) (z : V)
    (r : ↥(S \ {z} : Set V)) (a : S) : (G.induce (S \ {z})).ConnectedComponent := by
  classical
  exact if ha : a.1 ≠ z then
    (G.induce (S \ {z})).connectedComponentMk ⟨a.1, a.2, ha⟩ else
    (G.induce (S \ {z})).connectedComponentMk r

theorem carrierRetainedLabel_mem (G : SimpleGraph V) (S : Set V) (z : V)
    (r : ↥(S \ {z} : Set V)) (a : S) (ha : a.1 ≠ z) :
    carrierRetainedLabel G S z r a =
      (G.induce (S \ {z})).connectedComponentMk ⟨a.1, a.2, ha⟩ := by
  classical
  simp only [carrierRetainedLabel, dite_eq_left ha]

noncomputable def carrierDeletedLabel (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V) (r : ↥(S \ {z} : Set V))
    (v : {v : V // v ≠ z}) : (G.induce (S \ {z})).ConnectedComponent :=
  carrierRetainedLabel G S z r (carrierAnchor G S hS v.1)

theorem carrierDeletedLabel_mem (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V) (r : ↥(S \ {z} : Set V))
    (v : {v : V // v ≠ z}) (hv : v.1 ∈ S) :
    carrierDeletedLabel G S hS z r v =
      (G.induce (S \ {z})).connectedComponentMk ⟨v.1, hv, v.2⟩ := by
  unfold carrierDeletedLabel
  rw [carrierAnchor_mem G S hS v.1 hv]
  exact carrierRetainedLabel_mem G S z r ⟨v.1, hv⟩ v.2

theorem carrierDeletedLabel_adj (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V) (r : ↥(S \ {z} : Set V))
    {a b : {v : V // v ≠ z}} (e : (G.induce {v | v ≠ z}).Adj a b) :
    carrierDeletedLabel G S hS z r a = carrierDeletedLabel G S hS z r b := by
  rcases carrierAnchor_edge_cases G S hS e with he | ⟨ha, hb⟩
  · exact congrArg (carrierRetainedLabel G S z r) he
  · rw [carrierDeletedLabel_mem G S hS z r a ha,
      carrierDeletedLabel_mem G S hS z r b hb]
    exact ConnectedComponent.connectedComponentMk_eq_of_adj
      (G := G.induce (S \ {z})) (v := ⟨a.1, ha, a.2⟩) (w := ⟨b.1, hb, b.2⟩) e

theorem carrierDeletedLabel_walk (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V) (r : ↥(S \ {z} : Set V))
    {a b : {v : V // v ≠ z}} (p : (G.induce {v | v ≠ z}).Walk a b) :
    carrierDeletedLabel G S hS z r a = carrierDeletedLabel G S hS z r b := by
  induction p with
  | nil => rfl
  | cons e p ih => exact (carrierDeletedLabel_adj G S hS z r e).trans ih

theorem carrier_deleted_reachable (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V) (a b : ↥(S \ {z} : Set V))
    (hr : (G.induce {v | v ≠ z}).Reachable ⟨a.1, a.2.2⟩ ⟨b.1, b.2.2⟩) :
    (G.induce (S \ {z})).Reachable a b := by
  obtain ⟨p⟩ := hr
  have he := carrierDeletedLabel_walk G S hS z a p
  rw [carrierDeletedLabel_mem G S hS z a ⟨a.1, a.2.2⟩ a.2.1,
    carrierDeletedLabel_mem G S hS z a ⟨b.1, b.2.2⟩ b.2.1] at he
  exact ConnectedComponent.exact he

theorem carrier_deleted_connected (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : V) (r : ↥(S \ {z} : Set V))
    (hG : (G.induce {v | v ≠ z}).Connected) :
    (G.induce (S \ {z})).Connected := by
  refine { preconnected := ?_, nonempty := ⟨r⟩ }
  intro a b
  exact carrier_deleted_reachable G S hS z a b (hG ⟨a.1, a.2.2⟩ ⟨b.1, b.2.2⟩)

def carrierDeleteGraphIso (G : SimpleGraph V) (S : Set V) (z : S) :
    ((G.induce S).induce {v : S | v ≠ z}) ≃g G.induce (S \ {z.1}) where
  toEquiv := {
    toFun := fun v => ⟨v.1.1, v.1.2, fun he => v.2 (Subtype.ext he)⟩
    invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun he => v.2.2 (congrArg Subtype.val he)⟩
    left_inv := by intro v; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro v; apply Subtype.ext; rfl }
  map_rel_iff' := by intro a b; rfl

theorem carrier_nested_deleted_connected (G : SimpleGraph V) (S : Set V)
    (hS : SingleAttachmentCarrier G S) (z : S) (r : ↥(S \ {z.1} : Set V))
    (hG : (G.induce {v | v ≠ z.1}).Connected) :
    ((G.induce S).induce {v : S | v ≠ z}).Connected := by
  exact (carrierDeleteGraphIso G S z).connected_iff.mpr
    (carrier_deleted_connected G S hS z.1 r hG)

#print axioms carrierRetainedLabel
#print axioms carrierRetainedLabel_mem
#print axioms carrierDeletedLabel
#print axioms carrierDeletedLabel_mem
#print axioms carrierDeletedLabel_adj
#print axioms carrierDeletedLabel_walk
#print axioms carrier_deleted_reachable
#print axioms carrier_deleted_connected
#print axioms carrierDeleteGraphIso
#print axioms carrier_nested_deleted_connected
end TaskH.Gao
