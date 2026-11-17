import Research.TaskH.Critical

set_option autoImplicit false

universe u v

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} {α : Type v} {G : SimpleGraph V}

/-- Actual edges whose colors advance by a fixed color permutation. -/
def ColorStep (G : SimpleGraph V) (c : V → α) (σ : Equiv.Perm α) (x y : V) : Prop :=
  G.Adj x y ∧ c y = σ (c x)

/-- A successor-closed set can be shifted without making a monochromatic edge. -/
noncomputable def recolorClosed (c : G.Coloring α) (σ : Equiv.Perm α) (S : Set V)
    (hclosed : ∀ {x y : V}, x ∈ S → ColorStep G c σ x y → y ∈ S) :
    G.Coloring α := by
  classical
  refine SimpleGraph.Coloring.mk (fun x => if x ∈ S then σ (c x) else c x) ?_
  intro x y hxy
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp only [ite_eq_left hx, ite_eq_left hy]
    exact σ.injective.ne (c.valid hxy)
  · simp only [ite_eq_left hx, ite_eq_right hy]
    intro he
    exact hy (hclosed hx ⟨hxy, he.symm⟩)
  · simp only [ite_eq_right hx, ite_eq_left hy]
    intro he
    exact hx (hclosed hy ⟨hxy.symm, he⟩)
  · simp only [ite_eq_right hx, ite_eq_right hy]
    exact c.valid hxy

open scoped Classical in
theorem recolorClosed_apply (c : G.Coloring α) (σ : Equiv.Perm α) (S : Set V)
    (hclosed : ∀ {x y : V}, x ∈ S → ColorStep G c σ x y → y ∈ S) (x : V) :
    recolorClosed c σ S hclosed x = if x ∈ S then σ (c x) else c x := by
  classical
  rfl

/-- Criticality forces reachability between the two ends of a deleted edge.
Only the asserted change of the endpoint's color is required at this stage. -/
theorem critical_edge_reachable {k : ℕ} (h : IsCriticalPlus k G) {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k)) (σ : Equiv.Perm (Fin k))
    (hchange : σ (c x) ≠ c x) :
    Relation.ReflTransGen (ColorStep (G.deleteEdges {s(x, y)}) c σ) x y := by
  classical
  by_contra hnot
  let S : Set V := {z | Relation.ReflTransGen
    (ColorStep (G.deleteEdges {s(x, y)}) c σ) x z}
  have hclosed : ∀ {a b : V}, a ∈ S →
      ColorStep (G.deleteEdges {s(x, y)}) c σ a b → b ∈ S := by
    intro a b ha hab
    exact ha.tail hab
  let d := recolorClosed c σ S hclosed
  have hd : d x = d y := deletedEdge_coloring_endpoints h d
  have hx : x ∈ S := Relation.ReflTransGen.refl
  have hy : y ∉ S := hnot
  have hxv : d x = σ (c x) := by
    simpa only [ite_eq_left hx] using (recolorClosed_apply c σ S hclosed x)
  have hyv : d y = c y := by
    simpa only [ite_eq_right hy] using (recolorClosed_apply c σ S hclosed y)
  have he : σ (c x) = c y := hxv.symm.trans (hd.trans hyv)
  exact hchange (he.trans (deletedEdge_coloring_endpoints h c).symm)

#print axioms recolorClosed
#print axioms recolorClosed_apply
#print axioms critical_edge_reachable

end TaskH
