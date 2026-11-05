import Research.Backfill.Paper7.CycleFirstDart

set_option autoImplicit false

namespace Paper7Cycles

open SimpleGraph

variable {V : Type} [DecidableEq V] {H : SimpleGraph V}

/-- Removing a common first edge preserves edge-set inclusion when the left
walk is a trail, so that the removed edge does not occur in its tail. -/
theorem trail_tail_edgeFinset_subset {u v w : V} (huv huv' : H.Adj u v)
    (p q : H.Walk v w) (hp : (Walk.cons huv p).IsTrail)
    (he : (Walk.cons huv p).edges.toFinset ⊆ (Walk.cons huv' q).edges.toFinset) :
    p.edges.toFinset ⊆ q.edges.toFinset := by
  have hpnot : s(u, v) ∉ p.edges := (Walk.isTrail_cons huv p).mp hp |>.2
  intro e hem
  have hefull : e ∈ (Walk.cons huv' q).edges.toFinset :=
    he (by simp only [Walk.edges_cons, List.toFinset_cons]; exact Finset.mem_insert_of_mem hem)
  have hcases : e = s(u, v) ∨ e ∈ q.edges.toFinset := by
    simpa only [Walk.edges_cons, List.toFinset_cons, Finset.mem_insert] using hefull
  rcases hcases with hfirst | htail
  · subst e
    exact (hpnot (List.mem_toFinset.mp hem)).elim
  · exact htail

#print axioms Paper7Cycles.trail_tail_edgeFinset_subset

/-- Two simple paths with the same endpoints cannot have a proper edge-set
inclusion. In fact the original Walk objects must be equal. -/
theorem path_eq_of_edgeFinset_subset {u v : V} (p : H.Walk u v) :
    ∀ (q : H.Walk u v), p.IsPath → q.IsPath →
      p.edges.toFinset ⊆ q.edges.toFinset → p = q := by
  induction p with
  | nil =>
    intro q _ hq _
    exact (Walk.isPath_iff_nil.mp hq).eq_nil.symm
  | @cons u x v hux p ih =>
    intro q hp hq he
    cases q with
    | nil =>
      exact (Walk.not_nil_cons (Walk.isPath_iff_nil.mp hp)).elim
    | @cons _ y _ huy q =>
      have hxedge : s(u, x) ∈ (Walk.cons huy q).edges := by
        apply List.mem_toFinset.mp
        apply he
        simp [Walk.edges_cons]
      have hxy : x = y := by
        simpa only [Walk.snd_cons] using hq.eq_snd_of_mem_edges hxedge
      subst y
      have htail := trail_tail_edgeFinset_subset hux huy p q hp.isTrail he
      exact congrArg (fun t : H.Walk x v => Walk.cons hux t)
        (ih q hp.of_cons hq.of_cons htail)

#print axioms Paper7Cycles.path_eq_of_edgeFinset_subset

/-- Aligning the first dart turns inclusion of simple-cycle edge sets into
equality of the original Walk objects. -/
theorem cycle_eq_of_edgeFinset_subset_snd {u : V} {p q : H.Walk u u}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (he : p.edges.toFinset ⊆ q.edges.toFinset) (hs : p.snd = q.snd) : p = q := by
  cases p with
  | nil => exact (hp.ne_nil rfl).elim
  | @cons _ x _ hux p =>
    cases q with
    | nil => exact (hq.ne_nil rfl).elim
    | @cons _ y _ huy q =>
      have hxy : x = y := by simpa only [Walk.snd_cons] using hs
      subst y
      have hpt := (Walk.cons_isCycle_iff p hux).mp hp
      have hqt := (Walk.cons_isCycle_iff q huy).mp hq
      have htail := trail_tail_edgeFinset_subset hux huy p q hp.isTrail he
      exact congrArg (fun t : H.Walk x u => Walk.cons hux t)
        (path_eq_of_edgeFinset_subset p q hpt.1 hqt.1 htail)

#print axioms Paper7Cycles.cycle_eq_of_edgeFinset_subset_snd

/-- Simple-cycle edge sets are inclusion-minimal, even when their Walk
representatives have different starting vertices. -/
theorem cycle_edgeFinset_eq_of_subset {u v : V} {p : H.Walk u u} {q : H.Walk v v}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (he : p.edges.toFinset ⊆ q.edges.toFinset) : p.edges.toFinset = q.edges.toFinset := by
  let d := p.firstDart hp.not_nil
  have hd : d.edge ∈ q.edges := by
    apply List.mem_toFinset.mp
    apply he
    apply List.mem_toFinset.mpr
    exact p.mk_start_snd_mem_edges hp.not_nil
  obtain ⟨r, hr, _hrlen, hredges, hrsnd⟩ := cycle_with_first_dart q hq d hd
  have hpr : p.edges.toFinset ⊆ r.edges.toFinset := by
    rw [hredges]
    exact he
  have hp_eq_r : p = r := cycle_eq_of_edgeFinset_subset_snd hp hr hpr hrsnd.symm
  exact (congrArg (fun t : H.Walk u u => t.edges.toFinset) hp_eq_r).trans hredges

#print axioms Paper7Cycles.cycle_edgeFinset_eq_of_subset

end Paper7Cycles
