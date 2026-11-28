import Research.TaskV.Stanley.Refinement
import Research.TaskV.Stanley.Isolation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace StanleyContinuation
noncomputable section
open Finset

abbrev Cell {V C : Type*} (G : SimpleGraph V) (f : V → C) (c : C) :=
  G.induce {i : V | f i = c}

def cells {V C : Type*} (G : SimpleGraph V) (f : V → C) (c : C) :=
  Nat.card (Cell G f c).ConnectedComponent

theorem cell_card_pos {V C : Type*} [Finite V] {G : SimpleGraph V} {f : V → C} {c : C}
    (hc : 0 < histogram f c) : 0 < cells G f c := by
  obtain ⟨⟨v⟩,_⟩ := Nat.card_pos_iff.mp hc
  let : Nonempty (Cell G f c).ConnectedComponent :=
    ⟨(Cell G f c).connectedComponentMk v⟩
  exact Nat.card_pos

theorem cell_connected_iff {V C : Type*} [Finite V] {G : SimpleGraph V} {f : V → C} {c : C}
    (hc : 0 < histogram f c) : (Cell G f c).Connected ↔ cells G f c = 1 := by
  let K := Cell G f c
  obtain ⟨hv,_⟩ := Nat.card_pos_iff.mp hc
  constructor
  · intro h
    let := h.preconnected.subsingleton_connectedComponent
    let : Nonempty K.ConnectedComponent := hv.map K.connectedComponentMk
    exact Nat.card_unique
  · intro h
    obtain ⟨hs,_⟩ := Nat.card_eq_one_iff_unique.mp h
    exact (SimpleGraph.connected_iff _).mpr ⟨fun v w => SimpleGraph.ConnectedComponent.exact (hs.elim _ _), hv⟩

instance sizedFintype {V C : Type*} [Finite V] [Finite C] (s : C → ℕ) :
    Fintype (Sized (V := V) s) := Fintype.ofFinite _

theorem connCard_count {n k : ℕ} (G : SimpleGraph (Fin n)) (s : Fin k → ℕ)
    (hs : ∀ c, 0 < s c) :
    connectedCoefficient G k s =
      (Finset.univ.filter (fun f : Sized (V := Fin n) s => ∀ c, cells G f.1 c = 1)).card := by
  classical
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  refine {
    toFun := fun f => ⟨⟨f.1,funext (fun c => (f.2.1 c : histogram f.1 c = s c))⟩, ?_⟩
    invFun := fun f => ⟨f.1.1,congrFun f.1.2, ?_⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  · apply mem_filter.mpr
    refine ⟨mem_univ _, fun c => ?_⟩
    have hpos : 0 < histogram f.1 c := lt_of_lt_of_eq (hs c) (f.2.1 c).symm
    exact (cell_connected_iff hpos).mp (f.2.2 c)
  · intro c
    have hpos : 0 < histogram f.1.1 c := by rw [f.1.2]; exact hs c
    exact (cell_connected_iff hpos).mpr ((mem_filter.mp f.2).2 c)

theorem zero_cell_coefficient {n k : ℕ} (G : SimpleGraph (Fin n)) (s : Fin k → ℕ)
    (c : Fin k) (hc : s c = 0) : connectedCoefficient G k s = 0 := by
  classical
  apply Nat.eq_zero_of_not_pos
  intro h
  obtain ⟨⟨f, hf⟩,_⟩ := Nat.card_pos_iff.mp h
  have hpos : 0 < Nat.card {v : Fin n // f v = c} :=
    Nat.card_pos_iff.mpr ⟨(hf.2 c).nonempty, inferInstance⟩
  rw [hf.1 c, hc] at hpos
  exact (Nat.lt_irrefl _ hpos)

theorem groupColor_count {n k q : ℕ} (G : SimpleGraph (Fin n)) (s : Fin k → ℕ)
    (h : ∀ (f : Sized (V := Fin n) s) (c : Fin k),
      Nat.card (ProperAssignments (Cell G f.1 c) (Fin q)) =
        q ^ cells G f.1 c * (q-1) ^ (s c - cells G f.1 c)) :
    Nat.card (GroupColor (D := Fin q) G s) =
      ∑ f : Sized (V := Fin n) s, shadeWeight q s (cells G f.1) := by
  classical
  let (f : Sized (V := Fin n) s) (c : Fin k) :
      Fintype (ProperAssignments (Cell G f.1 c) (Fin q)) := Fintype.ofFinite _
  rw [Nat.card_congr (groupColorEquiv (D:=Fin q) G s)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_pi]
  apply sum_congr rfl
  intro f _
  unfold shadeWeight
  apply prod_congr rfl
  intro c _
  simpa [Nat.card_eq_fintype_card] using h f c

end
end StanleyContinuation
