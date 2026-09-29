import Research.Backfill.Paper4.Proof.DHExtensionCore

/-! Exact metric decomposition across a deleted separating vertex.
No finiteness or distance-hereditary assumption is needed for this bridge.
Compilation and acceptance are recorded separately. -/
set_option autoImplicit false

namespace CodexPaper4.CutVertexMetric
open SimpleGraph

theorem mem_support_of_not_reachable_delete {V : Type*} (G : SimpleGraph V)
    (v x y : V) (hx : x ≠ v) (hy : y ≠ v)
    (hn : ¬ (G.induce ({v}ᶜ : Set V)).Reachable
      (⟨x, hx⟩ : ({v}ᶜ : Set V)) ⟨y, hy⟩)
    (p : G.Walk x y) : v ∈ p.support := by
  classical
  by_contra hv
  have hw : ∀ z ∈ p.support, z ∈ ({v}ᶜ : Set V) := by
    intro z hz
    change z ≠ v
    intro hzv
    subst z
    exact hv hz
  exact hn ⟨p.induce ({v}ᶜ : Set V) hw⟩

theorem dist_eq_add_of_not_reachable_delete {V : Type*} (G : SimpleGraph V)
    (hc : G.Connected) (v x y : V) (hx : x ≠ v) (hy : y ≠ v)
    (hn : ¬ (G.induce ({v}ᶜ : Set V)).Reachable
      (⟨x, hx⟩ : ({v}ᶜ : Set V)) ⟨y, hy⟩) :
    G.dist x y = G.dist x v + G.dist v y := by
  apply le_antisymm (hc.dist_triangle (u := x) (v := v) (w := y))
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist x y
  have hmem := mem_support_of_not_reachable_delete G v x y hx hy hn p
  obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hmem
  have hlen : q.length + r.length = G.dist x y := by
    simpa only [hqr, SimpleGraph.Walk.length_append] using hp
  exact (Nat.add_le_add (SimpleGraph.dist_le q) (SimpleGraph.dist_le r)).trans_eq hlen

#print axioms dist_eq_add_of_not_reachable_delete
end CodexPaper4.CutVertexMetric
