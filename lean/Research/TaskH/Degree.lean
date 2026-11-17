import Research.TaskH.Critical

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

def neighborColor (v : V) (c : (G.induce {x | x ≠ v}).Coloring (Fin k))
    (z : G.neighborSet v) : Fin k :=
  c ⟨z.1, ((G.mem_neighborSet v z.1).mp z.2).ne.symm⟩

/-- Every color occurs on the neighbors of a deleted vertex, in every coloring. -/
theorem critical_neighborColor_surjective (h : IsCriticalPlus k G) (v : V)
    (c : (G.induce {x | x ≠ v}).Coloring (Fin k)) :
    Function.Surjective (neighborColor v c) := by
  classical
  intro i
  by_contra hmissing
  have hnot : ∀ z : G.neighborSet v, neighborColor v c z ≠ i := by
    intro z hz
    exact hmissing ⟨z, hz⟩
  apply critical_not_colorable h
  refine ⟨SimpleGraph.Coloring.mk (fun z => if hz : z = v then i else c ⟨z, hz⟩) ?_⟩
  intro a b hab
  by_cases ha : a = v
  · subst a
    have hb : b ≠ v := hab.ne.symm
    simpa [neighborColor, hb] using (hnot ⟨b, hab⟩).symm
  · by_cases hb : b = v
    · subst b
      simpa [neighborColor, ha] using hnot ⟨a, hab.symm⟩
    · simp only [dite_eq_right ha, dite_eq_right hb]
      exact c.valid hab

theorem critical_degree_ge [Fintype V] [DecidableRel G.Adj]
    (h : IsCriticalPlus k G) (v : V) : k ≤ G.degree v := by
  classical
  obtain ⟨c⟩ := critical_colorable_deletedVertex h v
  have hc := Fintype.card_le_of_surjective (neighborColor v c)
    (critical_neighborColor_surjective h v c)
  simpa only [Fintype.card_fin, G.card_neighborSet_eq_degree] using hc

#print axioms neighborColor
#print axioms critical_neighborColor_surjective
#print axioms critical_degree_ge

end TaskH
