import Research.Backfill.Paper7.CyclePathUniqueness

set_option autoImplicit false

noncomputable section

open SimpleGraph Finset
open scoped Classical

namespace Paper7Cycles

variable {V : Type} [DecidableEq V] {H : SimpleGraph V}

theorem rotate_edgeFinset {u v : V} (p : H.Walk u u) (hv : v ∈ p.support) :
    (p.rotate v hv).edges.toFinset = p.edges.toFinset := by
  apply Finset.ext
  intro e
  simpa only [List.mem_toFinset] using (p.rotate_edges v hv).perm.mem_iff (a := e)

#print axioms Paper7Cycles.rotate_edgeFinset

/-- Every dart belonging to the edge set of a cycle can be chosen as its first
dart, by rotating the cycle and, when necessary, reversing its orientation. -/
theorem cycle_with_first_dart {u : V} (p : H.Walk u u) (hp : p.IsCycle)
    (d : H.Dart) (hd : d.edge ∈ p.edges) :
    ∃ q : H.Walk d.fst d.fst,
      q.IsCycle ∧ q.length = p.length ∧ q.edges.toFinset = p.edges.toFinset ∧ q.snd = d.snd := by
  have hu : d.fst ∈ p.support := p.fst_mem_support_of_mem_edges hd
  let q := p.rotate d.fst hu
  have hq : q.IsCycle := hp.rotate hu
  have hlen : q.length = p.length := p.length_rotate d.fst hu
  have hedges : q.edges.toFinset = p.edges.toFinset := rotate_edgeFinset p hu
  have hdq : d.edge ∈ q.edges := by
    apply List.mem_toFinset.mp
    rw [hedges]
    exact List.mem_toFinset.mpr hd
  have hadj : q.toSubgraph.Adj d.fst d.snd := Walk.adj_toSubgraph_iff_mem_edges.mpr hdq
  have hneighbor : d.snd ∈ q.toSubgraph.neighborSet d.fst := hadj
  rw [hq.neighborSet_toSubgraph_endpoint] at hneighbor
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hneighbor
  rcases hneighbor with hfirst | hlast
  · exact ⟨q, hq, hlen, hedges, hfirst.symm⟩
  · refine ⟨q.reverse, hq.reverse, ?_, ?_, ?_⟩
    · simpa only [Walk.length_reverse] using hlen
    · simpa only [Walk.edges_reverse, List.toFinset_reverse] using hedges
    · rw [Walk.snd_reverse]
      exact hlast.symm

#print axioms Paper7Cycles.cycle_with_first_dart

/-- A cycle has exactly as many distinct possible starting vertices as edges. -/
theorem cycle_support_card {u : V} (p : H.Walk u u) (hp : p.IsCycle) :
    p.support.toFinset.card = p.length := by
  have hu : u ∈ p.support.tail := p.end_mem_tail_support hp.not_nil
  have hmem : u ∈ p.support.tail.toFinset := List.mem_toFinset.mpr hu
  have heq : p.support.toFinset = p.support.tail.toFinset := by
    have h := congrArg List.toFinset p.cons_tail_support
    simpa only [List.toFinset_cons, Finset.insert_eq_of_mem hmem] using h.symm
  rw [heq, List.toFinset_card_of_nodup hp.support_nodup,
    List.length_tail, Walk.length_support, Nat.add_sub_cancel]

#print axioms Paper7Cycles.cycle_support_card

/-- At a fixed starting vertex, a cycle edge set permits only the reference
orientation and its reversal. -/
theorem cycle_eq_or_eq_reverse_of_edgeFinset {u : V} {p q : H.Walk u u}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (he : p.edges.toFinset = q.edges.toFinset) : q = p ∨ q = p.reverse := by
  have hedge : s(u, q.snd) ∈ p.edges := by
    apply List.mem_toFinset.mp
    rw [he]
    exact List.mem_toFinset.mpr (q.mk_start_snd_mem_edges hq.not_nil)
  have hn : q.snd ∈ p.toSubgraph.neighborSet u :=
    Walk.adj_toSubgraph_iff_mem_edges.mpr hedge
  rw [hp.neighborSet_toSubgraph_endpoint] at hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with hfirst | hlast
  · exact Or.inl (cycle_eq_of_edgeFinset_snd hq hp he.symm hfirst)
  · apply Or.inr
    apply cycle_eq_of_edgeFinset_snd hq hp.reverse
    · simpa only [Walk.edges_reverse, List.toFinset_reverse] using he.symm
    · simpa only [Walk.snd_reverse] using hlast

#print axioms Paper7Cycles.cycle_eq_or_eq_reverse_of_edgeFinset

omit [DecidableEq V] in
/-- The two orientations are distinct for every Mathlib simple cycle. -/
theorem cycle_ne_reverse {u : V} (p : H.Walk u u) (hp : p.IsCycle) :
    p ≠ p.reverse := by
  intro heq
  have h := congrArg (fun q : H.Walk u u => q.snd) heq
  exact hp.snd_ne_penultimate (by simpa only [Walk.snd_reverse] using h)

#print axioms Paper7Cycles.cycle_ne_reverse

/-- At each supported vertex, the entire set of cycles with the prescribed
edge set consists of the rotation of the reference cycle and its reverse. -/
theorem cycles_at_vertex_eq_pair {u v : V} (p : H.Walk u u) (hp : p.IsCycle)
    (hv : v ∈ p.support) :
    {q : H.Walk v v | q.IsCycle ∧ q.edges.toFinset = p.edges.toFinset} =
      {p.rotate v hv, (p.rotate v hv).reverse} := by
  let r := p.rotate v hv
  have hr : r.IsCycle := hp.rotate hv
  have hre : r.edges.toFinset = p.edges.toFinset := rotate_edgeFinset p hv
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hq, hqe⟩
    exact cycle_eq_or_eq_reverse_of_edgeFinset hr hq (hre.trans hqe.symm)
  · rintro (rfl | rfl)
    · exact ⟨hr, hre⟩
    · exact ⟨hr.reverse, by simpa only [Walk.edges_reverse, List.toFinset_reverse] using hre⟩

#print axioms Paper7Cycles.cycles_at_vertex_eq_pair

/-- There are exactly two orientations at each possible starting vertex. -/
theorem cycles_at_vertex_ncard {u v : V} (p : H.Walk u u) (hp : p.IsCycle)
    (hv : v ∈ p.support) :
    {q : H.Walk v v | q.IsCycle ∧ q.edges.toFinset = p.edges.toFinset}.ncard = 2 := by
  rw [cycles_at_vertex_eq_pair p hp hv]
  exact Set.ncard_pair (cycle_ne_reverse (p.rotate v hv) (hp.rotate hv))

#print axioms Paper7Cycles.cycles_at_vertex_ncard

end Paper7Cycles
