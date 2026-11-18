import Research.TaskH.Fan.Challenge

/-! Graph isomorphisms transport the actual finite-cardinality and every-delete tests. -/
set_option autoImplicit false
universe u v
namespace TaskH.Gao
open SimpleGraph TaskH.Fan
variable {V : Type u} {W : Type v}

def deleteVertexGraphIso (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) (y : W) :
    G.induce {x : V | x ≠ e.symm y} ≃g H.induce {z : W | z ≠ y} where
  toEquiv := {
    toFun := fun x => ⟨e x.1, by
      intro he
      apply x.2
      apply e.toEquiv.injective
      exact he.trans (e.toEquiv.apply_symm_apply y).symm⟩
    invFun := fun z => ⟨e.symm z.1, fun he => z.2 (e.toEquiv.symm.injective he)⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact e.toEquiv.symm_apply_apply x.1
    right_inv := by
      intro z
      apply Subtype.ext
      exact e.toEquiv.apply_symm_apply z.1 }
  map_rel_iff' := by
    intro a b
    change H.Adj (e a.1) (e b.1) ↔ G.Adj a.1 b.1
    exact e.map_rel_iff

theorem twoConnected_of_graphIso [iV : Fintype V] [iW : Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    (hG : @TwoConnected V iV G) : @TwoConnected W iW H := by
  have heq : Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
  have hc : 3 ≤ Fintype.card W := by
    rw [← heq]
    exact hG.1
  refine ⟨hc, e.connected_iff.mp hG.2.1, ?_⟩
  intro y
  exact (deleteVertexGraphIso G H e y).connected_iff.mp (hG.2.2 (e.symm y))

theorem twoConnected_graphIso_iff [iV : Fintype V] [iW : Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H) :
    @TwoConnected V iV G ↔ @TwoConnected W iW H := by
  constructor
  · exact twoConnected_of_graphIso (V := V) (W := W) (iV := iV) (iW := iW) G H e
  · exact twoConnected_of_graphIso (V := W) (W := V) (iV := iW) (iW := iV) H G e.symm

#print axioms deleteVertexGraphIso
#print axioms twoConnected_of_graphIso
#print axioms twoConnected_graphIso_iff
end TaskH.Gao
