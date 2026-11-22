import Research.TaskP.PrimeMedialRacks.CoordinatesCore
import Research.TaskP.PrimeMedialRacks.DisplacementData

namespace TaskP.PrimeMedialRacks
open Challenge

private def recast {n m : ℕ} {G : Type*} [Group G] (h : n=m)
    (e : Multiplicative (ZMod n) ≃* G) : Multiplicative (ZMod m) ≃* G := h ▸ e

theorem regular_affine {p : ℕ} [Fact p.Prime] (op : Operation (Fin p)) (hr : IsRack op)
    (hn : ¬TwoReductive op) (D : RegularDisplacements op hr) :
    ∃ k : Parameter p, Isomorphic op (affine k.1) := by
  classical
  let base : Fin p := 0
  let orb : D.group ≃ Fin p := Equiv.ofBijective _ (D.regular base)
  have card : Nat.card D.group = p := (Nat.card_congr orb).trans (by simp)
  have cyc := isCyclic_of_prime_card card
  let coord : Multiplicative (ZMod p) ≃* D.group :=
    recast card (zmodCyclicMulEquiv cyc)
  let d : ZMod p → D.group := fun t => coord (Multiplicative.ofAdd t)
  have dadd (t y : ZMod p) : d (t+y) = d t * d y := coord.map_mul _ _
  let e : ZMod p ≃ Fin p := (Multiplicative.ofAdd.trans coord.toEquiv).trans orb
  have ee (y : ZMod p) : e y = (d y).1 base := rfl
  have tr (t y : ZMod p) : (d t).1 (e y) = e (t+y) := by
    rw [ee y, ee (t+y), dadd]
    rfl
  let O : Operation (ZMod p) := fun x y => e.symm (op (e x) (e y))
  have eO (x y : ZMod p) : e (O x y) = op (e x) (e y) := e.apply_symm_apply _
  have iso : Isomorphic O op := ⟨e,eO⟩
  have sh (t x y : ZMod p) : O (t+x) (t+y) = t+O x y := by
    apply e.injective
    rw [eO, ← tr, ← tr, ← tr, eO, D.acts _ (d t).2]
  have nz (t : ZMod p) : ∃ w, ∀ y, O 0 (t+y) = w + O 0 y := by
    let L := leftPerm hr (e 0)
    let g : D.group := ⟨L * (d t).1 * L⁻¹,D.normalizes (e 0) _ (d t).2⟩
    let w : ZMod p := (coord.symm g).toAdd
    have hw : d w = g := coord.apply_symm_apply g
    refine ⟨w,fun y => e.injective ?_⟩
    rw [eO,← tr,← tr,eO,hw]
    change L ((d t).1 (e y)) = ((L * (d t).1) * L⁻¹) (L (e y))
    simp
  obtain ⟨k,hk⟩ := normalized_coordinates O (iso_rack (iso_symm iso) hr)
    (fun h => hn (iso_reductive iso h)) sh nz
  exact ⟨k,iso_trans (iso_symm iso) ⟨Equiv.refl _,hk⟩⟩

end TaskP.PrimeMedialRacks
