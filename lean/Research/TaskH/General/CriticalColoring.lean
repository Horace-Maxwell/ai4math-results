import Research.TaskH.Critical

/-! Color gluing in the original full-critical graph. No graph oracle is assumed. -/
set_option autoImplicit false
universe u
namespace TaskH.General
open SimpleGraph TaskH.Challenge
variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

theorem critical_colorable_proper_induce (h : IsCriticalPlus k G)
    (S : Set V) (hS : S ≠ Set.univ) : (G.induce S).Colorable k := by
  rw [SimpleGraph.induce_eq_coe_induce_top]
  apply h.2 _
  intro heq
  apply hS
  ext v
  constructor
  · intro _
    trivial
  · intro _
    have hv : v ∈ ((⊤ : G.Subgraph).induce S).verts := by
      rw [heq]
      exact Set.mem_univ v
    exact hv

theorem critical_card_gt [Fintype V] (h : IsCriticalPlus k G) :
    k < Fintype.card V := by
  by_contra hn
  exact TaskH.critical_not_colorable h
    (SimpleGraph.Colorable.mono (Nat.le_of_not_gt hn) (SimpleGraph.colorable_of_fintype G))

theorem colorable_glue_at_vertex (G : SimpleGraph V) (S T : Set V) (z : V)
    (hzS : z ∈ S) (hzT : z ∈ T)
    (hcover : ∀ v : V, v ∈ S ∨ v ∈ T)
    (hinter : ∀ v : V, v ∈ S → v ∈ T → v = z)
    (hedge : ∀ a b : V, G.Adj a b → (a ∈ S ∧ b ∈ S) ∨ (a ∈ T ∧ b ∈ T))
    (hS : (G.induce S).Colorable k) (hT : (G.induce T).Colorable k) :
    G.Colorable k := by
  classical
  obtain ⟨cS⟩ := hS
  obtain ⟨cT⟩ := hT
  let τ : Fin k ≃ Fin k := Equiv.swap (cT ⟨z, hzT⟩) (cS ⟨z, hzS⟩)
  let f : V → Fin k := fun v => if hv : v ∈ S then cS ⟨v, hv⟩
    else τ (cT ⟨v, (hcover v).resolve_left hv⟩)
  have hfS : ∀ v : V, ∀ hv : v ∈ S, f v = cS ⟨v, hv⟩ := by
    intro v hv
    simp only [f, dite_eq_left hv]
  have hfT : ∀ v : V, ∀ hv : v ∈ T, f v = τ (cT ⟨v, hv⟩) := by
    intro v hv
    by_cases hs : v ∈ S
    · have he := hinter v hs hv
      subst v
      rw [hfS z hzS]
      exact (Equiv.swap_apply_left _ _).symm
    · simp only [f, dite_eq_right hs]
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro a b hab
  rcases hedge a b hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [hfS a ha, hfS b hb]
    exact cS.valid hab
  · rw [hfT a ha, hfT b hb]
    intro he
    have hne : cT ⟨a, ha⟩ ≠ cT ⟨b, hb⟩ := cT.valid hab
    exact hne (τ.injective he)

#print axioms critical_colorable_proper_induce
#print axioms critical_card_gt
#print axioms colorable_glue_at_vertex
end TaskH.General
