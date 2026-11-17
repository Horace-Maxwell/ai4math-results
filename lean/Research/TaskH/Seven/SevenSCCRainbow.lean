import Research.TaskH.Seven.Definitions
import Research.TaskH.Seven.SevenSCCPalette

/-!
Universal rainbow transport from the original deleted-vertex condition
to every deleted-edge coloring on a circle avoiding either endpoint.
-/

set_option autoImplicit false

universe u

namespace TaskH.Seven

open SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

noncomputable def deletedEdgeColoringAwayLeft {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) :
    (G.induce {z | z ≠ x}).Coloring (Fin 7) := by
  classical
  refine SimpleGraph.Coloring.mk (fun z => c z.val) ?_
  intro a b hab
  apply c.valid
  refine SimpleGraph.deleteEdges_adj.mpr ⟨hab, ?_⟩
  intro he
  have heq : s(a.val, b.val) = s(x, y) := Set.mem_singleton_iff.mp he
  rcases Sym2.eq_iff.mp heq with ⟨ha, _⟩ | ⟨_, hb⟩
  · exact a.property ha
  · exact b.property hb

noncomputable def deletedEdgeColoringAwayRight {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) :
    (G.induce {z | z ≠ y}).Coloring (Fin 7) := by
  classical
  refine SimpleGraph.Coloring.mk (fun z => c z.val) ?_
  intro a b hab
  apply c.valid
  refine SimpleGraph.deleteEdges_adj.mpr ⟨hab, ?_⟩
  intro he
  have heq : s(a.val, b.val) = s(x, y) := Set.mem_singleton_iff.mp he
  rcases Sym2.eq_iff.mp heq with ⟨_, hb⟩ | ⟨ha, _⟩
  · exact b.property hb
  · exact a.property ha

/-- This holds for every proper coloring of the actual deleted-edge graph,
not just for one originally chosen coloring. -/
theorem deletedEdge_rainbow_of_avoids (hr : RainbowSevenCycles G)
    {x y z : V} (p : G.Walk z z) (hp : p.IsCycle) (hl : p.length = 7)
    (hav : x ∉ p.support ∨ y ∉ p.support)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) :
    Set.InjOn c {a | a ∈ p.support} := by
  intro a ha b hb he
  rcases hav with hx | hy
  · have hax : a ≠ x := fun h => hx (h ▸ ha)
    have hbx : b ≠ x := fun h => hx (h ▸ hb)
    exact congrArg Subtype.val
      (hr x (deletedEdgeColoringAwayLeft c) p hp hl
        ⟨a, hax⟩ ⟨b, hbx⟩ ha hb he)
  · have hay : a ≠ y := fun h => hy (h ▸ ha)
    have hby : b ≠ y := fun h => hy (h ▸ hb)
    exact congrArg Subtype.val
      (hr y (deletedEdgeColoringAwayRight c) p hp hl
        ⟨a, hay⟩ ⟨b, hby⟩ ha hb he)

/-- Any injective seven-point parametrization of this actual circle is
rainbow in every deleted-edge coloring, including every closed recolor. -/
theorem deletedEdge_trace_injective (hr : RainbowSevenCycles G)
    {x y z : V} (p : G.Walk z z) (hp : p.IsCycle) (hl : p.length = 7)
    (hav : x ∉ p.support ∨ y ∉ p.support)
    (f : Fin 7 → V) (hf : Function.Injective f)
    (hm : ∀ i : Fin 7, f i ∈ p.support)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7)) :
    Function.Injective (fun i => c (f i)) := by
  intro i j he
  exact hf (deletedEdge_rainbow_of_avoids hr p hp hl hav c (hm i) (hm j) he)

/-- Actual original-graph transport to mutual successor reachability on
every nonbad circle. The finite trace carries no new graph hypothesis. -/
theorem deletedEdge_trace_reachable (hr : RainbowSevenCycles G)
    {x y z : V} (p : G.Walk z z) (hp : p.IsCycle) (hl : p.length = 7)
    (hav : x ∉ p.support ∨ y ∉ p.support)
    (f : Fin 7 → V) (hf : Function.Injective f)
    (hm : ∀ i : Fin 7, f i ∈ p.support)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin 7))
    (σ : Equiv.Perm (Fin 7))
    (horbit : ∀ a b : Fin 7, ∃ n : ℕ, (σ ^ n) a = b) (i j : Fin 7) :
    Relation.ReflTransGen (ColorStep (G.deleteEdges {s(x, y)}) c σ) (f i) (f j) := by
  have hinj := deletedEdge_trace_injective hr p hp hl hav f hf hm c
  have hbij : Function.Bijective (fun i => c (f i)) :=
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  apply trace_reachable_of_all_closed_recolors c f hbij σ horbit
  intro S hclosed
  exact deletedEdge_trace_injective hr p hp hl hav f hf hm
    (recolorClosed c σ S (@hclosed))

end TaskH.Seven

#print axioms TaskH.Seven.deletedEdgeColoringAwayLeft
#print axioms TaskH.Seven.deletedEdgeColoringAwayRight
#print axioms TaskH.Seven.deletedEdge_rainbow_of_avoids
#print axioms TaskH.Seven.deletedEdge_trace_injective
#print axioms TaskH.Seven.deletedEdge_trace_reachable
