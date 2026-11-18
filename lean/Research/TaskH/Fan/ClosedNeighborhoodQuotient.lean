import Research.TaskH.Fan.RootNeighborhood
import Research.TaskH.Fan.IdentificationConnectivity

/-! Original hypotheses internally give the actual closed-neighborhood quotient frame. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

theorem closedNeighborhood_quotient_connected [Fintype V] (G : SimpleGraph V)
    (hG : TwoConnected G) (x : V) :
    (identificationGraph G (closedRootNeighborhood G x)).Connected := by
  exact identification_connected G (closedRootNeighborhood G x) ⟨x, Or.inl rfl⟩ hG.2.1

theorem closedNeighborhood_quotient_delete_retained [Fintype V] (G : SimpleGraph V)
    (hG : TwoConnected G) (x : V) :
    ∀ w : IdentificationVertex (closedRootNeighborhood G x), w ≠ none →
      ((identificationGraph G (closedRootNeighborhood G x)).induce {v | v ≠ w}).Connected := by
  intro w hw
  cases w with
  | none => exact False.elim (hw rfl)
  | some w =>
    exact identification_delete_retained_connected G (closedRootNeighborhood G x)
      ⟨x, Or.inl rfl⟩ w.1 w.2 (hG.2.2 w.1)

theorem closedNeighborhood_quotient_degree (G : SimpleGraph V) (x y : V)
    (hxy : x ≠ y) (hno : ¬G.Adj x y) (hfour : ¬rootFourCycleAvoiding G x y)
    (hdeg : NonrootDegreeAtLeast G x y 3) :
    NonrootDegreeAtLeast (identificationGraph G (closedRootNeighborhood G x)) none
      (some ⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩) 3 := by
  intro w hwn hwy
  cases w with
  | none => exact False.elim (hwn rfl)
  | some w =>
    have hwy' : w.1 ≠ y := by
      intro he
      have hs : w = (⟨y, closedRootNeighborhood_other_root_out G x y hxy hno⟩ :
          {v : V // v ∉ closedRootNeighborhood G x}) := Subtype.ext he
      exact hwy (congrArg Option.some hs)
    have hwx : w.1 ≠ x := fun he => w.2 (Or.inl he)
    have heq := identification_neighbor_ncard G (closedRootNeighborhood G x) w
      (fun a b ha hb e e' => noFour_closed_neighbors_unique G x y hxy hno hfour
        w.1 w.2 hwy' ha hb e e')
    rw [← heq]
    exact hdeg w.1 hwx hwy'

theorem closedNeighborhood_quotient_card [Fintype V] (G : SimpleGraph V)
    (hG : TwoConnected G) (x y : V) (hxy : x ≠ y)
    [Fintype {v : V // v ∉ closedRootNeighborhood G x}] :
    Fintype.card (IdentificationVertex (closedRootNeighborhood G x)) < Fintype.card V := by
  classical
  let : Fintype (closedRootNeighborhood G x) := Fintype.ofFinite _
  have hX := closedRootNeighborhood_card G hG x y hxy
  have hle := Fintype.card_subtype_le (fun v : V => v ∈ closedRootNeighborhood G x)
  have hc := Fintype.card_subtype_compl (fun v : V => v ∈ closedRootNeighborhood G x)
  have ho : Fintype.card (IdentificationVertex (closedRootNeighborhood G x)) =
      Fintype.card {v : V // v ∉ closedRootNeighborhood G x} + 1 := Fintype.card_option
  simp only [Fintype.card_eq_nat_card] at hX hle hc ho ⊢
  let e : (closedRootNeighborhood G x) ≃ {v : V // v ∈ closedRootNeighborhood G x} := {
    toFun := fun v => ⟨v.1, v.2⟩
    invFun := fun v => ⟨v.1, v.2⟩
    left_inv := fun v => Subtype.ext rfl
    right_inv := fun v => Subtype.ext rfl }
  have hcoecard := Nat.card_congr e
  have hXmem : 3 ≤ Nat.card {v : V // v ∈ closedRootNeighborhood G x} :=
    hcoecard ▸ hX
  omega

#print axioms closedNeighborhood_quotient_connected
#print axioms closedNeighborhood_quotient_delete_retained
#print axioms closedNeighborhood_quotient_degree
#print axioms closedNeighborhood_quotient_card
end TaskH.Fan
