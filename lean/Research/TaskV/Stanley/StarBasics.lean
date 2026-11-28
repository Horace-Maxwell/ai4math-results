import Research.TaskV.Stanley.ProfileDefs

namespace StanleyContinuation
open SimpleGraph Finset
open scoped BigOperators
noncomputable section

variable {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}

@[simp] theorem mem_stanleyNeighbors : u ∈ neighbors G v ↔ G.Adj v u := by
  classical simp [neighbors]
@[simp] theorem mem_stanleyCore : v ∈ core G ↔ (neighbors G v).card ≠ 1 := by
  classical simp [core]

theorem stanley_neighbors_card (G : SimpleGraph (Fin n)) (v : Fin n) :
    (neighbors G v).card = Nat.card (G.neighborSet v) := by
  classical
  rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
  rw [SimpleGraph.degree]
  congr 1
  ext u
  simp

theorem outsideCore_iff_uniqueAdj (G : SimpleGraph (Fin n)) (v : Fin n) :
    v ∉ core G ↔ ∃! u, G.Adj v u := by
  classical
  simp only [mem_stanleyCore, not_not]
  rw [stanley_neighbors_card, Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
  exact G.degree_eq_one_iff_existsUnique_adj

theorem reachable_closed {α : Type*} {H : SimpleGraph α} {x y : α}
    (P : α → Prop) (h : H.Reachable x y) (hx : P x)
    (move : ∀ a b, P a → H.Adj a b → P b) : P y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | cons adj _ ih => exact ih (move _ _ hx adj)

theorem leaf_neighbor_in_core (hG : G.Connected) (hc : (core G).Nonempty)
    (hu : u ∉ core G) (huv : G.Adj u v) : v ∈ core G := by
  by_contra hv
  obtain ⟨a,ha,ha'⟩ := (outsideCore_iff_uniqueAdj G u).mp hu
  obtain ⟨b,hb,hb'⟩ := (outsideCore_iff_uniqueAdj G v).mp hv
  obtain ⟨t,ht⟩ := hc
  have ht' : t = u ∨ t = v := reachable_closed (fun x => x = u ∨ x = v)
    (hG.preconnected u t) (Or.inl rfl) (by
      intro p q hp he
      rcases hp with rfl | rfl
      · exact Or.inr ((ha' q he).trans (ha' v huv).symm)
      · exact Or.inl ((hb' q he).trans (hb' u huv.symm).symm))
  rcases ht' with rfl | rfl <;> contradiction

/-- The ordinary nonleaf vertex to which a vertex belongs. -/
def starCenter (hG : G.Connected) (hc : (core G).Nonempty) (x : Fin n) : ↥(core G) := by
  classical
  by_cases h : x ∈ core G
  · exact ⟨x,h⟩
  · let a := ((outsideCore_iff_uniqueAdj G x).mp h).exists
    exact ⟨a.choose, leaf_neighbor_in_core hG hc h a.choose_spec⟩

@[simp] theorem starCenter_core (hG : G.Connected) (hc : (core G).Nonempty)
    (x : ↥(core G)) : starCenter hG hc x = x := by
  classical
  simp [starCenter, x.property]

theorem starCenter_leaf (hG : G.Connected) (hc : (core G).Nonempty)
    (hx : u ∉ core G) : G.Adj u (starCenter hG hc u) := by
  classical
  simpa [starCenter,hx] using ((outsideCore_iff_uniqueAdj G u).mp hx).exists.choose_spec

theorem starCenter_leaf_eq (hG : G.Connected) (hc : (core G).Nonempty)
    (hx : u ∉ core G) (hadj : G.Adj u v) : (starCenter hG hc u : Fin n) = v := by
  obtain ⟨a,_,ha⟩ := (outsideCore_iff_uniqueAdj G u).mp hx
  exact (ha _ (starCenter_leaf hG hc hx)).trans (ha _ hadj).symm

theorem starCenter_iff (hG : G.Connected) (hc : (core G).Nonempty)
    (x : Fin n) (c : ↥(core G)) :
    starCenter hG hc x = c ↔ x = c ∨ x ∉ core G ∧ G.Adj x c := by
  classical
  by_cases hx : x ∈ core G
  · let a : ↥(core G) := ⟨x,hx⟩
    have hh : starCenter hG hc x = a := starCenter_core hG hc a
    simp [hh, hx, Subtype.ext_iff, a]
  · have hne : x ≠ c := fun he => hx (he ▸ c.property)
    simp only [hne,false_or,hx,not_false_eq_true,true_and]
    constructor
    · intro h
      simpa [← h] using starCenter_leaf hG hc hx
    · intro h
      exact Subtype.ext (starCenter_leaf_eq hG hc hx h)

theorem starCenter_fiber_card (hG : G.Connected) (hc : (core G).Nonempty)
    (c : ↥(core G)) :
    Nat.card {x : Fin n // starCenter hG hc x = c} = coreWeight G c := by
  classical
  have hs : univ.filter (fun x => starCenter hG hc x = c) =
      insert (c : Fin n) ((neighbors G c) \ core G) := by
    ext x
    simp [starCenter_iff, and_comm, SimpleGraph.adj_comm]
  have hnot : (c : Fin n) ∉ (neighbors G c) \ core G := by simp [c.property]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hs, card_insert_of_notMem hnot]
  simp [coreWeight,Nat.add_comm]

end
end StanleyContinuation
