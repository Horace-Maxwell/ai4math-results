import Research.TaskH.General.EdgeColorOrders
import Research.TaskH.Basics

/-!
The critical-edge recoloring argument is used for every genuine k-color
cyclic order. The witnesses are actual graph cycles, with the second
endpoint absent from their actual support.
-/

set_option autoImplicit false

universe u

namespace TaskH.General

open _root_.TaskH.Challenge SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

/-- Internal short-cycle interface, to be derived from original equality hypotheses.
It is not added to any frozen Main or Challenge statement. -/
def ShortCycles (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ {x : V} (p : G.Walk x x), p.IsCycle → k ∣ p.length → p.length = k

theorem critical_edge_reachable_from_right (h : IsCriticalPlus k G) {x y : V}
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k)) (σ : Equiv.Perm (Fin k))
    (hchange : σ (c y) ≠ c y) :
    Relation.ReflTransGen (ColorStep (G.deleteEdges {s(x, y)}) c σ) y x := by
  classical
  by_contra hnot
  let S : Set V := {z | Relation.ReflTransGen
    (ColorStep (G.deleteEdges {s(x, y)}) c σ) y z}
  have hclosed : ∀ {a b : V}, a ∈ S →
      ColorStep (G.deleteEdges {s(x, y)}) c σ a b → b ∈ S := by
    intro a b ha hab
    exact ha.tail hab
  let d := recolorClosed c σ S hclosed
  have hd : d x = d y := deletedEdge_coloring_endpoints h d
  have hy : y ∈ S := Relation.ReflTransGen.refl
  have hx : x ∉ S := hnot
  have hxv : d x = c x := by
    simpa only [ite_eq_right hx] using (recolorClosed_apply c σ S hclosed x)
  have hyv : d y = σ (c y) := by
    simpa only [ite_eq_left hy] using (recolorClosed_apply c σ S hclosed y)
  have he : σ (c y) = c x := hyv.symm.trans (hd.symm.trans hxv)
  exact hchange (he.trans (deletedEdge_coloring_endpoints h c))

theorem follows_cycle_avoids_same_color (hk : 3 ≤ k) {x y : V} (p : G.Walk x x)
    (c : V → Fin k) (hf : Follows p c (finRotate k))
    (hl : p.length = k) (he : c y = c x) (hne : x ≠ y) : y ∉ p.support := by
  intro hy
  obtain ⟨n, hn, hny⟩ := List.mem_iff_getElem.mp hy
  have hn' : n ≤ p.length := by
    rw [Walk.length_support] at hn
    omega
  have hv : p.getVert n = y := (p.getVert_eq_support_getElem hn').trans hny
  have hc : ((finRotate k) ^ n) (c x) = c x :=
    (follows_getVert p c (finRotate k) hf n hn').symm.trans
      ((congrArg c hv).trans he)
  have hd : k ∣ n := (rotate_pow_fixed_iff hk (c x) n).mp hc
  have hnends : n = 0 ∨ n = k := by
    by_cases hz : n = 0
    · exact Or.inl hz
    · have hkn : k ≤ n := Nat.le_of_dvd (by omega : 0 < n) hd
      exact Or.inr (by omega)
  rcases hnends with hn0 | hnk
  · exact hne (by simpa only [hn0, Walk.getVert_zero] using hv)
  · have hend : p.getVert k = x := by simpa only [hl] using p.getVert_length
    exact hne (hend.symm.trans (hnk ▸ hv))

/-- This actual witness retains its chosen rank order for later singleton
arguments; it is stronger than the numerical E bound alone. -/
theorem critical_edge_ordered_cycle (hk : 3 ≤ k) (h : IsCriticalPlus k G) (hs : ShortCycles k G)
    {x y : V} (hxy : G.Adj x y)
    (c : (G.deleteEdges {s(x, y)}).Coloring (Fin k)) (π : Equiv.Perm (Fin k)) :
    ∃ q : G.Walk x x, q.IsCycle ∧ q.length = k ∧
      Follows q (fun z => π (c z)) (finRotate k) ∧ y ∉ q.support := by
  let σ := orderedColorCycle π
  have hmono : ColorStep (G.deleteEdges {s(x, y)}) c σ ≤ ColorStep G c σ := by
    intro a b hab
    exact ⟨(SimpleGraph.deleteEdges_adj.mp hab.1).1, hab.2⟩
  have hrxy := Relation.ReflTransGen.mono hmono x y
    (critical_edge_reachable h c σ (orderedColorCycle_no_fixed hk π (c x)))
  have hryx := Relation.ReflTransGen.mono hmono y x
    (critical_edge_reachable_from_right h c σ (orderedColorCycle_no_fixed hk π (c y)))
  obtain ⟨p, hp⟩ := reach_exists_follows_walk c σ hrxy
  obtain ⟨r, hr⟩ := reach_exists_follows_walk c σ hryx
  have hpos : 0 < p.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hxy.ne)
  have hnon : p.append r ≠ .nil := by
    intro heq
    have hz := congrArg Walk.length heq
    simp only [Walk.length_append, Walk.length_nil] at hz
    omega
  have hf := (follows_append p r c σ).mpr ⟨hp, hr⟩
  obtain ⟨q, hq, hqf⟩ := follows_closed_exists_cycle (p.append r) hnon c σ hf
    (orderedColorCycle_no_two_step hk π (c x))
  have hqrank : Follows q (fun z => π (c z)) (finRotate k) :=
    (follows_orderedColorCycle_iff q c π).mp hqf
  have hlen := hs q hq (follows_rotate_length_dvd hk q _ hqrank)
  refine ⟨q, hq, hlen, hqrank, ?_⟩
  exact follows_cycle_avoids_same_color hk q _ hqrank hlen
    (congrArg π (deletedEdge_coloring_endpoints h c).symm) hxy.ne

theorem mem_modCyclesThroughAvoid_of_cycle [DecidableEq V] {x y : V}
    {p : G.Walk x x} (hp : p.IsCycle) (hlen : p.length = k) (hy : y ∉ p.support) :
    p.edges.toFinset ∈ TaskH.modCyclesThroughAvoid k G x y := by
  refine ⟨(Basics.cycle_edges_mem_modCycleEdgeSets_iff hp).mpr ?_, ?_, ?_⟩
  · simpa only [hlen] using (dvd_refl k)
  · exact (TaskH.cycleContains_edges_toFinset_iff p hp.not_nil x).mpr p.start_mem_support
  · intro he
    exact hy ((TaskH.cycleContains_edges_toFinset_iff p hp.not_nil y).mp he)

end TaskH.General

#print axioms TaskH.General.ShortCycles
#print axioms TaskH.General.critical_edge_reachable_from_right
#print axioms TaskH.General.follows_cycle_avoids_same_color
#print axioms TaskH.General.critical_edge_ordered_cycle
#print axioms TaskH.General.mem_modCyclesThroughAvoid_of_cycle
