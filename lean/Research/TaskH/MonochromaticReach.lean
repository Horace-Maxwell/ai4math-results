import Research.TaskH.Recolor

set_option autoImplicit false

universe u

namespace TaskH

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

/-- The arbitrary-label recoloring lemma used by the original good-cycle
construction. The set M specifies an orientation of every monochromatic edge;
it need not consist of all ordered monochromatic edges. -/
theorem noncolorable_reach_between_monoEdges (hnot : ¬ G.Colorable k)
    (c : V → Fin k) (σ : Equiv.Perm (Fin k)) (M : Set (V × V))
    (hcover : ∀ {x y : V}, G.Adj x y → c x = c y →
      (x, y) ∈ M ∨ (y, x) ∈ M) :
    ∃ e ∈ M, ∃ f ∈ M, Relation.ReflTransGen (ColorStep G c σ) e.1 f.2 := by
  classical
  by_contra hex
  let S : Set V := {z | ∃ e ∈ M, Relation.ReflTransGen (ColorStep G c σ) e.1 z}
  have htail : ∀ e ∈ M, e.1 ∈ S := by
    intro e he
    exact ⟨e, he, Relation.ReflTransGen.refl⟩
  have hhead : ∀ f ∈ M, f.2 ∉ S := by
    intro f hf hmem
    obtain ⟨e, he, hreach⟩ := hmem
    exact hex ⟨e, he, f, hf, hreach⟩
  have hclosed : ∀ {x y : V}, x ∈ S → ColorStep G c σ x y → y ∈ S := by
    intro x y hx hxy
    obtain ⟨e, he, hreach⟩ := hx
    exact ⟨e, he, hreach.tail hxy⟩
  have hseparate : ∀ {x y : V}, G.Adj x y → c x = c y →
      (x ∈ S ∧ y ∉ S) ∨ (y ∈ S ∧ x ∉ S) := by
    intro x y hxy heq
    rcases hcover hxy heq with h | h
    · exact Or.inl ⟨htail (x, y) h, hhead (x, y) h⟩
    · exact Or.inr ⟨htail (y, x) h, hhead (y, x) h⟩
  apply hnot
  refine ⟨SimpleGraph.Coloring.mk (fun x => if x ∈ S then σ (c x) else c x) ?_⟩
  intro x y hxy
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp only [ite_eq_left hx, ite_eq_left hy]
    intro heq
    rcases hseparate hxy (σ.injective heq) with hs | hs
    · exact hs.2 hy
    · exact hs.2 hx
  · simp only [ite_eq_left hx, ite_eq_right hy]
    intro heq
    exact hy (hclosed hx ⟨hxy, heq.symm⟩)
  · simp only [ite_eq_right hx, ite_eq_left hy]
    intro heq
    exact hx (hclosed hy ⟨hxy.symm, heq⟩)
  · simp only [ite_eq_right hx, ite_eq_right hy]
    intro heq
    rcases hseparate hxy heq with hs | hs
    · exact hx hs.1
    · exact hy hs.1

#print axioms noncolorable_reach_between_monoEdges

end TaskH
