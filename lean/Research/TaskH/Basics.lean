import Research.TaskH.Challenge

/-!
Semantic bridges for the frozen Task H statements.

The finite objects counted are undirected edge sets of genuine cycles.
Neither a starting point nor a direction is retained in that representation.
This module proves only foundational bridges, not an equality case.
-/

universe u

namespace TaskH.Basics

variable {V : Type u} {G : SimpleGraph V}

/-- The collection in the frozen definition is genuinely finite on finite graphs. -/
theorem modCycleEdgeSets_finite [Finite V] (k : ℕ) (G : SimpleGraph V) :
    (Challenge.ModCycleEdgeSets k G).Finite := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact Set.toFinite _

section DecidableVertices

variable [DecidableEq V]

/-- A genuine cycle has as many distinct undirected edges as walk steps. -/
theorem cycle_edges_toFinset_card {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) : p.edges.toFinset.card = p.length := by
  calc
    p.edges.toFinset.card = p.edges.length :=
      List.toFinset_card_of_nodup hp.isCircuit.isTrail.edges_nodup
    _ = p.length := p.length_edges

/-- The edge-set predicate in the frozen statement has a genuine cycle witness. -/
theorem isCycleEdgeSet_iff_exists_walk {s : Finset (Sym2 V)} :
    Challenge.IsCycleEdgeSet G s ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.edges.toFinset = s := by
  classical
  simp only [Challenge.IsCycleEdgeSet, Finset.ext_iff, List.mem_toFinset]

/-- The equivalent set-valued formulation does not choose walk representatives. -/
theorem isCycleEdgeSet_iff_exists_walk_edgeSet {s : Finset (Sym2 V)} :
    Challenge.IsCycleEdgeSet G s ↔
      ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.edgeSet = (s : Set (Sym2 V)) := by
  classical
  rw [isCycleEdgeSet_iff_exists_walk]
  constructor
  · rintro ⟨v, p, hp, hs⟩
    refine ⟨v, p, hp, ?_⟩
    rw [← p.coe_edges_toFinset, hs]
  · rintro ⟨v, p, hp, hs⟩
    refine ⟨v, p, hp, Finset.coe_injective ?_⟩
    rw [p.coe_edges_toFinset]
    exact hs

/-- The original divisibility condition counts every divisible length. -/
theorem mem_modCycleEdgeSets_iff {k : ℕ} {s : Finset (Sym2 V)} :
    s ∈ Challenge.ModCycleEdgeSets k G ↔
      ∃ (v : V) (p : G.Walk v v),
        p.IsCycle ∧ p.edges.toFinset = s ∧ k ∣ p.length := by
  classical
  change (Challenge.IsCycleEdgeSet G s ∧ k ∣ s.card) ↔ _
  rw [isCycleEdgeSet_iff_exists_walk]
  constructor
  · rintro ⟨⟨v, p, hp, hs⟩, hk⟩
    refine ⟨v, p, hp, hs, ?_⟩
    rw [← hs, cycle_edges_toFinset_card hp] at hk
    exact hk
  · rintro ⟨v, p, hp, hs, hk⟩
    refine ⟨⟨v, p, hp, hs⟩, ?_⟩
    rw [← hs, cycle_edges_toFinset_card hp]
    exact hk

/-- A fixed cycle is counted precisely when its walk length is divisible by k. -/
theorem cycle_edges_mem_modCycleEdgeSets_iff {k : ℕ} {v : V}
    {p : G.Walk v v} (hp : p.IsCycle) :
    p.edges.toFinset ∈ Challenge.ModCycleEdgeSets k G ↔ k ∣ p.length := by
  classical
  change (Challenge.IsCycleEdgeSet G p.edges.toFinset ∧
    k ∣ p.edges.toFinset.card) ↔ _
  rw [cycle_edges_toFinset_card hp]
  have hc : Challenge.IsCycleEdgeSet G p.edges.toFinset :=
    isCycleEdgeSet_iff_exists_walk.mpr ⟨v, p, hp, rfl⟩
  exact and_iff_right hc

/-- Reversing direction produces the identical finite undirected edge set. -/
theorem reverse_edges_toFinset {v w : V} (p : G.Walk v w) :
    p.reverse.edges.toFinset = p.edges.toFinset := by
  ext e
  simp [SimpleGraph.Walk.edges_reverse]

/-- Changing the starting point produces the identical finite edge set. -/
theorem rotate_edges_toFinset {v : V} (p : G.Walk v v) (w : V)
    (hw : w ∈ p.support) :
    (p.rotate w hw).edges.toFinset = p.edges.toFinset := by
  ext e
  simp only [List.mem_toFinset]
  exact (p.rotate_edges w hw).perm.mem_iff

/-- The frozen count does not distinguish the reverse traversal. -/
theorem reverse_mem_modCycleEdgeSets_iff {k : ℕ} {v : V} (p : G.Walk v v) :
    p.reverse.edges.toFinset ∈ Challenge.ModCycleEdgeSets k G ↔
      p.edges.toFinset ∈ Challenge.ModCycleEdgeSets k G := by
  rw [reverse_edges_toFinset]

/-- The frozen count does not distinguish another starting vertex. -/
theorem rotate_mem_modCycleEdgeSets_iff {k : ℕ} {v : V}
    (p : G.Walk v v) (w : V) (hw : w ∈ p.support) :
    (p.rotate w hw).edges.toFinset ∈ Challenge.ModCycleEdgeSets k G ↔
      p.edges.toFinset ∈ Challenge.ModCycleEdgeSets k G := by
  rw [rotate_edges_toFinset]

end DecidableVertices

end TaskH.Basics

#print axioms TaskH.Basics.modCycleEdgeSets_finite
#print axioms TaskH.Basics.cycle_edges_toFinset_card
#print axioms TaskH.Basics.mem_modCycleEdgeSets_iff
#print axioms TaskH.Basics.reverse_edges_toFinset
#print axioms TaskH.Basics.rotate_edges_toFinset
