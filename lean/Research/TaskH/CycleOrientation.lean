import Research.TaskH.Challenge

/-!
Uniqueness of a genuine simple cycle up to starting point and direction.

The argument uses ordinary paths and the cycle subgraph's two neighbors at
each vertex. No special four-cycle representation occurs in this module.
-/

universe u

namespace TaskH.CycleOrientation

variable {V : Type u} {G : SimpleGraph V}

/-- A nonempty walk's edge set determines its entire subgraph. -/
theorem toSubgraph_eq_of_edgeSet_eq {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d}
    (hp : ¬ p.Nil) (hq : ¬ q.Nil) (h : p.edgeSet = q.edgeSet) :
    p.toSubgraph = q.toSubgraph := by
  apply le_antisymm
  · apply (SimpleGraph.Walk.toSubgraph_le_iff (w := p) hp).mpr
    simpa only [SimpleGraph.Walk.edgeSet_toSubgraph] using h.le
  · apply (SimpleGraph.Walk.toSubgraph_le_iff (w := q) hq).mpr
    simpa only [SimpleGraph.Walk.edgeSet_toSubgraph] using h.ge

/-- Trails with the same first edge permit that edge to be removed from the comparison. -/
theorem cons_tail_edgeSet_eq {a b c : V} {hab hab' : G.Adj a b}
    {p q : G.Walk b c}
    (hp : (SimpleGraph.Walk.cons hab p).IsTrail)
    (hq : (SimpleGraph.Walk.cons hab' q).IsTrail)
    (h : (SimpleGraph.Walk.cons hab p).edgeSet =
      (SimpleGraph.Walk.cons hab' q).edgeSet) :
    p.edgeSet = q.edgeSet := by
  classical
  have hpn : s(a, b) ∉ p.edges :=
    ((SimpleGraph.Walk.isTrail_cons hab p).mp hp).2
  have hqn : s(a, b) ∉ q.edges :=
    ((SimpleGraph.Walk.isTrail_cons hab' q).mp hq).2
  ext e
  by_cases he : e = s(a, b)
  · subst e
    exact iff_of_false hpn hqn
  · have hm := Set.ext_iff.mp h e
    simpa only [SimpleGraph.Walk.edgeSet_cons, Set.mem_insert_iff, he, false_or] using hm

/-- A simple path with fixed endpoints is determined by its undirected edge set. -/
theorem path_eq_of_edgeSet_eq {a b : V} (p : G.Walk a b) :
    ∀ q : G.Walk a b, p.IsPath → q.IsPath → p.edgeSet = q.edgeSet → p = q := by
  induction p with
  | nil =>
    intro q hp hq h
    cases q with
    | nil => rfl
    | cons hab q =>
      simp only [SimpleGraph.Walk.edgeSet_nil, SimpleGraph.Walk.edgeSet_cons] at h
      have hm : (∅ : Set (Sym2 V)).Nonempty := by
        rw [h]
        exact ⟨_, Or.inl rfl⟩
      rcases hm with ⟨e, he⟩
      exact he.elim
  | @cons a b c hab p ih =>
    intro q hp hq h
    cases q with
    | nil =>
      simp only [SimpleGraph.Walk.edgeSet_nil, SimpleGraph.Walk.edgeSet_cons] at h
      have hm : (∅ : Set (Sym2 V)).Nonempty := by
        rw [← h]
        exact ⟨_, Or.inl rfl⟩
      rcases hm with ⟨e, he⟩
      exact he.elim
    | @cons _ b' _ hab' q =>
      have hm : s(a, b') ∈ (SimpleGraph.Walk.cons hab p).edges := by
        change s(a, b') ∈ (SimpleGraph.Walk.cons hab p).edgeSet
        rw [h]
        simp
      have hb : b' = b := by
        simpa only [SimpleGraph.Walk.snd_cons] using hp.eq_snd_of_mem_edges hm
      subst b'
      have ht : p.edgeSet = q.edgeSet := cons_tail_edgeSet_eq hp.isTrail hq.isTrail h
      have hp' : p.IsPath := hp.of_cons
      have hq' : q.IsPath := hq.of_cons
      have heq : p = q := ih q hp' hq' ht
      cases heq
      rfl

/-- At a fixed base vertex, a second cycle can leave in only the two existing directions. -/
theorem cycle_snd_eq_or_eq_penultimate {a : V} {p q : G.Walk a a}
    (hp : p.IsCycle) (hq : q.IsCycle) (h : p.edgeSet = q.edgeSet) :
    q.snd = p.snd ∨ q.snd = p.penultimate := by
  have hsg := toSubgraph_eq_of_edgeSet_eq hp.not_nil hq.not_nil h
  have hadj : p.toSubgraph.Adj a q.snd := by
    rw [hsg]
    exact q.toSubgraph_adj_snd hq.not_nil
  have hm : q.snd ∈ p.toSubgraph.neighborSet a := hadj
  rw [hp.neighborSet_toSubgraph_endpoint] at hm
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hm

/-- With a fixed base and first step, a genuine simple cycle is unique. -/
theorem cycle_eq_of_snd_eq {a : V} {p q : G.Walk a a}
    (hp : p.IsCycle) (hq : q.IsCycle) (h : p.edgeSet = q.edgeSet)
    (hs : p.snd = q.snd) : p = q := by
  cases p with
  | nil => exact (hp.ne_nil rfl).elim
  | @cons a b _ hab p =>
    cases q with
    | nil => exact (hq.ne_nil rfl).elim
    | @cons _ b' _ hab' q =>
      have hb : b = b' := by simpa only [SimpleGraph.Walk.snd_cons] using hs
      subst b'
      have hp' : p.IsPath := ((SimpleGraph.Walk.cons_isCycle_iff p hab).mp hp).1
      have hq' : q.IsPath := ((SimpleGraph.Walk.cons_isCycle_iff q hab').mp hq).1
      have ht : p.edgeSet = q.edgeSet :=
        cons_tail_edgeSet_eq hp.isCircuit.isTrail hq.isCircuit.isTrail h
      have heq : p = q := path_eq_of_edgeSet_eq p q hp' hq' ht
      cases heq
      rfl

/-- A based genuine simple cycle has exactly the two possible traversals of its edge set. -/
theorem cycle_eq_or_reverse {a : V} {p q : G.Walk a a}
    (hp : p.IsCycle) (hq : q.IsCycle) (h : p.edgeSet = q.edgeSet) :
    q = p ∨ q = p.reverse := by
  rcases cycle_snd_eq_or_eq_penultimate hp hq h with hs | hs
  · exact Or.inl (cycle_eq_of_snd_eq hp hq h hs.symm).symm
  · have he : p.reverse.edgeSet = q.edgeSet := by
      simpa only [SimpleGraph.Walk.edgeSet_reverse] using h
    have hs' : p.reverse.snd = q.snd := by
      simpa only [SimpleGraph.Walk.snd_reverse] using hs.symm
    exact Or.inr (cycle_eq_of_snd_eq hp.reverse hq he hs').symm

section DecidableVertices

variable [DecidableEq V]

/-- Equality of the frozen finite edge sets gives equality of ordinary edge sets. -/
theorem edgeSet_eq_of_toFinset_eq {a b c d : V}
    {p : G.Walk a b} {q : G.Walk c d}
    (h : p.edges.toFinset = q.edges.toFinset) : p.edgeSet = q.edgeSet := by
  rw [← p.coe_edges_toFinset, ← q.coe_edges_toFinset, h]

/-- Genuine cycles with the same edge set differ only by base vertex and direction. -/
theorem cycle_eq_rotate_or_reverse {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle) (h : p.edgeSet = q.edgeSet) :
    ∃ hb : b ∈ p.support, q = p.rotate b hb ∨ q = (p.rotate b hb).reverse := by
  have hsg := toSubgraph_eq_of_edgeSet_eq hp.not_nil hq.not_nil h
  have hb : b ∈ p.support := by
    have hm : b ∈ p.toSubgraph.verts := by
      rw [hsg]
      exact q.start_mem_verts_toSubgraph
    exact p.mem_verts_toSubgraph.mp hm
  refine ⟨hb, ?_⟩
  have hp' : (p.rotate b hb).IsCycle :=
    (SimpleGraph.Walk.isCycle_rotate hb).mpr hp
  have he : (p.rotate b hb).edgeSet = q.edgeSet := by
    calc
      (p.rotate b hb).edgeSet = (p.rotate b hb).toSubgraph.edgeSet :=
        (SimpleGraph.Walk.edgeSet_toSubgraph _).symm
      _ = p.toSubgraph.edgeSet := by rw [SimpleGraph.Walk.toSubgraph_rotate]
      _ = p.edgeSet := SimpleGraph.Walk.edgeSet_toSubgraph _
      _ = q.edgeSet := h
  exact cycle_eq_or_reverse hp' hq he

/-- The same uniqueness theorem for the exact finite edge-set representation in Challenge. -/
theorem cycle_eq_rotate_or_reverse_of_toFinset_eq
    {a b : V} {p : G.Walk a a} {q : G.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (h : p.edges.toFinset = q.edges.toFinset) :
    ∃ hb : b ∈ p.support, q = p.rotate b hb ∨ q = (p.rotate b hb).reverse :=
  cycle_eq_rotate_or_reverse hp hq (edgeSet_eq_of_toFinset_eq h)

end DecidableVertices

end TaskH.CycleOrientation

#print axioms TaskH.CycleOrientation.path_eq_of_edgeSet_eq
#print axioms TaskH.CycleOrientation.cycle_eq_of_snd_eq
#print axioms TaskH.CycleOrientation.cycle_eq_or_reverse
#print axioms TaskH.CycleOrientation.cycle_eq_rotate_or_reverse_of_toFinset_eq
