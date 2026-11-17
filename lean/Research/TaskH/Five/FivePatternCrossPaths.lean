import Research.TaskH.Five.FiveAttachedGroup

/-! Transport a finite cross-edge table to paths through actual pattern vertices. -/

set_option autoImplicit false

universe u

namespace TaskH.Five

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

theorem pattern_cross_path {P : Finset (Sym2 (Fin 5))} {f : Fin 5 → V}
    (hf : PatternEmbedding G P f) (A : Finset (Fin 5) → Prop)
    (htable : ∀ I J : Finset (Fin 5), A I → A J →
      ∃ i ∈ I, ∃ j ∈ J, s(i, j) ∈ P)
    (x y : V) (hx : A (patternNeighborIndices G f x))
    (hy : A (patternNeighborIndices G f y)) :
    ∃ i j : Fin 5, G.Adj x (f i) ∧ G.Adj (f i) (f j) ∧ G.Adj (f j) y := by
  obtain ⟨i, hi, j, hj, hij⟩ :=
    htable (patternNeighborIndices G f x) (patternNeighborIndices G f y) hx hy
  exact ⟨i, j, (Finset.mem_filter.mp hi).2, hf.2 i j hij,
    (Finset.mem_filter.mp hj).2.symm⟩

theorem attachedGroup_cross_paths {P : Finset (Sym2 (Fin 5))} {f : Fin 5 → V}
    (hf : PatternEmbedding G P f) (a : Fin 5) (R : Finset V)
    (A : Finset (Fin 5) → Prop)
    (htable : ∀ I J : Finset (Fin 5), A I → A J →
      ∃ i ∈ I, ∃ j ∈ J, s(i, j) ∈ P)
    (hanchor : A (patternNeighborIndices G f (f a)))
    (hR : ∀ x ∈ R, A (patternNeighborIndices G f x)) :
    ∀ x ∈ attachedGroup f a R, ∀ y ∈ attachedGroup f a R, x ≠ y →
      ∃ i j : Fin 5, G.Adj x (f i) ∧ G.Adj (f i) (f j) ∧ G.Adj (f j) y := by
  have hZ : ∀ x ∈ attachedGroup f a R, A (patternNeighborIndices G f x) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hm
    · simpa only [he] using hanchor
    · exact hR x hm
  intro x hx y hy _hxy
  exact pattern_cross_path hf A htable x y (hZ x hx) (hZ y hy)

end TaskH.Five

#print axioms TaskH.Five.pattern_cross_path
#print axioms TaskH.Five.attachedGroup_cross_paths
