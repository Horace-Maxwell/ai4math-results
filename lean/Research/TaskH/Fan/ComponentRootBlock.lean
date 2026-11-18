import Research.TaskH.Fan.RootedSetRetraction

/-!
An actual connected component of K-z, with z adjoined, is an induced block
under connectedness of K and connectedness after every retained deletion.
The component is the Mathlib quotient component, not an assumed cover.
-/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

def componentRootSet (K : SimpleGraph V) (z : V)
    (C : (K.induce {v | v ≠ z}).ConnectedComponent) : Set V :=
  {v | v = z ∨ ∃ h : v ≠ z, (⟨v, h⟩ : {w : V // w ≠ z}) ∈ C.supp}

theorem componentRootSet_closed (K : SimpleGraph V) (z : V)
    (C : (K.induce {v | v ≠ z}).ConnectedComponent) :
    ∀ a ∈ componentRootSet K z C, a ≠ z → ∀ b, K.Adj a b →
      b ∈ componentRootSet K z C := by
  intro a ha haz b hab
  rcases ha with ha | ⟨_ha', haC⟩
  · exact False.elim (haz ha)
  · by_cases hbz : b = z
    · exact Or.inl hbz
    · exact Or.inr ⟨hbz, C.mem_supp_of_adj_mem_supp haC hab⟩

theorem componentRoot_connected (K : SimpleGraph V) (z : V)
    (C : (K.induce {v | v ≠ z}).ConnectedComponent) (hK : K.Connected) :
    (K.induce (componentRootSet K z C)).Connected := by
  exact rootedSet_connected K (componentRootSet K z C) z (Or.inl rfl)
    (componentRootSet_closed K z C) hK

theorem componentRoot_delete_retained_connected (K : SimpleGraph V) (z : V)
    (C : (K.induce {v | v ≠ z}).ConnectedComponent)
    (w : componentRootSet K z C) (hw : w.1 ≠ z)
    (hK : (K.induce {v | v ≠ w.1}).Connected) :
    ((K.induce (componentRootSet K z C)).induce {v | v ≠ w}).Connected := by
  exact rootedSet_delete_connected K (componentRootSet K z C) z (Or.inl rfl)
    (componentRootSet_closed K z C) w hw hK

theorem componentRoot_delete_root_connected (K : SimpleGraph V) (z : V)
    (C : (K.induce {v | v ≠ z}).ConnectedComponent) :
    ((K.induce (componentRootSet K z C)).induce
      {v | v ≠ (⟨z, Or.inl rfl⟩ : componentRootSet K z C)}).Connected := by
  let f : C → {b : componentRootSet K z C //
      b ≠ (⟨z, Or.inl rfl⟩ : componentRootSet K z C)} := fun a =>
    ⟨⟨a.1.1, Or.inr ⟨a.1.2, a.2⟩⟩, by
      intro he
      exact a.1.2 (congrArg Subtype.val he)⟩
  have hf : Function.Surjective f := by
    intro b
    rcases b.1.2 with hb | ⟨hb, hbC⟩
    · exact False.elim (b.2 (Subtype.ext hb))
    · refine ⟨⟨⟨b.1.1, hb⟩, hbC⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl
  have he : ∀ {a b : C}, C.toSimpleGraph.Adj a b →
      f a = f b ∨
        ((K.induce (componentRootSet K z C)).induce
          {v | v ≠ (⟨z, Or.inl rfl⟩ : componentRootSet K z C)}).Adj (f a) (f b) := by
    intro a b hab
    exact Or.inr hab
  exact connected_of_surjective_adj_or_eq f hf he C.connected_toSimpleGraph

theorem componentRoot_neighbor_ncard (K : SimpleGraph V) (z : V)
    (C : (K.induce {v | v ≠ z}).ConnectedComponent)
    (t : {v : V // v ≠ z}) (ht : t ∈ C.supp) :
    (K.neighborSet t.1).ncard =
      ((K.induce (componentRootSet K z C)).neighborSet
        ⟨t.1, Or.inr ⟨t.2, ht⟩⟩).ncard := by
  exact rootedSet_neighbor_ncard K (componentRootSet K z C) z
    (componentRootSet_closed K z C) ⟨t.1, Or.inr ⟨t.2, ht⟩⟩ t.2

theorem componentRoot_twoConnected [Fintype V] (K : SimpleGraph V) (z : V)
    (C : (K.induce {v | v ≠ z}).ConnectedComponent)
    [Fintype (componentRootSet K z C)] (hT : 2 ≤ C.supp.ncard)
    (hK : K.Connected)
    (hd : ∀ w : V, w ≠ z → (K.induce {v | v ≠ w}).Connected) :
    TwoConnected (K.induce (componentRootSet K z C)) := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Set.one_lt_ncard_iff (s := C.supp)).mp (show 1 < C.supp.ncard by omega)
  let zr : componentRootSet K z C := ⟨z, Or.inl rfl⟩
  let ar : componentRootSet K z C := ⟨a.1, Or.inr ⟨a.2, ha⟩⟩
  let br : componentRootSet K z C := ⟨b.1, Or.inr ⟨b.2, hb⟩⟩
  have hza : zr ≠ ar := by
    intro he
    exact a.2 (congrArg Subtype.val he).symm
  have hzb : zr ≠ br := by
    intro he
    exact b.2 (congrArg Subtype.val he).symm
  have hab' : ar ≠ br := by
    intro he
    have hv : a.1 = b.1 := congrArg
      (fun w : componentRootSet K z C => w.1) he
    exact hab (Subtype.ext hv)
  have hcard : 2 < Fintype.card (componentRootSet K z C) :=
    Fintype.two_lt_card_iff.mpr ⟨zr, ar, br, hza, hzb, hab'⟩
  refine ⟨by omega, componentRoot_connected K z C hK, ?_⟩
  intro w
  by_cases hw : w.1 = z
  · have he : w = (⟨z, Or.inl rfl⟩ : componentRootSet K z C) := Subtype.ext hw
    subst w
    exact componentRoot_delete_root_connected K z C
  · exact componentRoot_delete_retained_connected K z C w hw (hd w.1 hw)

#print axioms componentRootSet
#print axioms componentRootSet_closed
#print axioms componentRoot_connected
#print axioms componentRoot_delete_retained_connected
#print axioms componentRoot_delete_root_connected
#print axioms componentRoot_neighbor_ncard
#print axioms componentRoot_twoConnected
end TaskH.Fan
