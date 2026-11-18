import Research.TaskH.Fan.AdjEqConnectivity
import Research.TaskH.Fan.PathOperations

/-! The actual G-Q component, and actual simple tails with no other outside vertex. -/
set_option autoImplicit false
universe u
namespace TaskH.Fan
open SimpleGraph
variable {V : Type u}

def outsideComponent (G : SimpleGraph V) (Q : Set V) (y : V) (hy : y ∉ Q) : Set V :=
  {v | ∃ hv : v ∉ Q,
    (⟨v, hv⟩ : {w : V // w ∉ Q}) ∈
      ((G.induce Qᶜ).connectedComponentMk ⟨y, hy⟩).supp}

theorem outsideComponent_not_mem (G : SimpleGraph V) (Q : Set V) (y : V) (hy : y ∉ Q)
    {v : V} (hv : v ∈ outsideComponent G Q y hy) : v ∉ Q := by
  obtain ⟨hvQ, _hvC⟩ := hv
  exact hvQ

theorem outsideComponent_root_mem (G : SimpleGraph V) (Q : Set V) (y : V) (hy : y ∉ Q) :
    y ∈ outsideComponent G Q y hy := ⟨hy, rfl⟩

theorem outsideComponent_closed (G : SimpleGraph V) (Q : Set V) (y : V) (hy : y ∉ Q)
    {v w : V} (hv : v ∈ outsideComponent G Q y hy) (hw : w ∉ Q)
    (e : G.Adj v w) : w ∈ outsideComponent G Q y hy := by
  obtain ⟨hvQ, hvC⟩ := hv
  exact ⟨hw, ((G.induce Qᶜ).connectedComponentMk ⟨y, hy⟩).mem_supp_of_adj_mem_supp hvC e⟩

theorem outsideComponent_connected (G : SimpleGraph V) (Q : Set V) (y : V) (hy : y ∉ Q) :
    (G.induce (outsideComponent G Q y hy)).Connected := by
  let C : (G.induce Qᶜ).ConnectedComponent := (G.induce Qᶜ).connectedComponentMk ⟨y, hy⟩
  let T := {v : {w : V // w ∉ Q} // v ∈ C.supp}
  let f : T → outsideComponent G Q y hy := fun v => ⟨v.1.1, ⟨v.1.2, v.2⟩⟩
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨hv, hvC⟩ := v.2
    exact ⟨⟨⟨v.1, hv⟩, hvC⟩, Subtype.ext rfl⟩
  have he : ∀ {a b : T}, C.toSimpleGraph.Adj a b →
      f a = f b ∨ (G.induce (outsideComponent G Q y hy)).Adj (f a) (f b) := by
    intro a b e
    exact Or.inr e
  exact connected_of_surjective_adj_or_eq f hf he C.connected_toSimpleGraph

theorem component_induced_support (G : SimpleGraph V) (C : Set V) {s t : C}
    (p : (G.induce C).Walk s t) :
    ∀ v ∈ (p.map (SimpleGraph.Embedding.induce C).toHom).support, v ∈ C := by
  intro v hv
  rw [Walk.support_map] at hv
  obtain ⟨w, _hw, hwv⟩ := List.mem_map.mp hv
  exact hwv ▸ w.2

theorem connectedSet_positive_tail (G : SimpleGraph V) (C : Set V)
    (hC : (G.induce C).Connected) (p y : V) (hp : p ∉ C) (hy : y ∈ C)
    (hedge : ∃ z ∈ C, G.Adj p z) :
    ∃ r : G.Walk p y, r.IsPath ∧ 1 ≤ r.length ∧
      ∀ w, w ∈ r.support → w ≠ p → w ∈ C := by
  obtain ⟨z, hz, epz⟩ := hedge
  obtain ⟨t, ht⟩ := (hC (⟨z, hz⟩ : C) ⟨y, hy⟩).exists_isPath
  let t' : G.Walk z y := t.map (SimpleGraph.Embedding.induce C).toHom
  have ht' : t'.IsPath :=
    (Walk.isPath_map_iff_of_injective Subtype.val_injective).mpr ht
  have hp' : p ∉ t'.support := fun h => hp (component_induced_support G C t p h)
  refine ⟨Walk.cons epz t', ht'.cons hp', ?_, ?_⟩
  · simp only [Walk.length_cons]
    omega
  · intro w hw hwp
    rw [Walk.support_cons] at hw
    rcases List.mem_cons.mp hw with he | he
    · exact False.elim (hwp he)
    · exact component_induced_support G C t w he

#print axioms outsideComponent
#print axioms outsideComponent_not_mem
#print axioms outsideComponent_root_mem
#print axioms outsideComponent_closed
#print axioms outsideComponent_connected
#print axioms component_induced_support
#print axioms connectedSet_positive_tail
end TaskH.Fan
