import Research.TaskH.Fan.Challenge

/-!
Reachability transport permits an actual edge to collapse to equal vertices.
Only reachability is transported, with no preserved-length assertion.
-/
set_option autoImplicit false
universe u v
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u} {W : Type v} {G : SimpleGraph V} {K : SimpleGraph W}

theorem reachable_map_of_adj_or_eq (f : V → W)
    (hf : ∀ {a b : V}, G.Adj a b → f a = f b ∨ K.Adj (f a) (f b))
    {x y : V} (h : G.Reachable x y) : K.Reachable (f x) (f y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.rfl
  | cons h _ ih =>
    rcases hf h with he | he
    · rw [he]
      exact ih
    · exact he.reachable.trans ih

theorem connected_of_surjective_adj_or_eq (f : V → W) (hs : Function.Surjective f)
    (hf : ∀ {a b : V}, G.Adj a b → f a = f b ∨ K.Adj (f a) (f b))
    (h : G.Connected) : K.Connected := by
  obtain ⟨v⟩ := h.nonempty
  refine { preconnected := ?_, nonempty := ⟨f v⟩ }
  intro a b
  obtain ⟨x, rfl⟩ := hs a
  obtain ⟨y, rfl⟩ := hs b
  exact reachable_map_of_adj_or_eq f hf (h x y)

#print axioms reachable_map_of_adj_or_eq
#print axioms connected_of_surjective_adj_or_eq
end TaskH.Fan
