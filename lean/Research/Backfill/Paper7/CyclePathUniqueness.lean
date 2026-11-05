import Mathlib

set_option autoImplicit false

noncomputable section

open SimpleGraph Finset
open scoped Classical

namespace Paper7Cycles

variable {V : Type} [DecidableEq V] {H : SimpleGraph V}

theorem trail_tail_edgeFinset_eq {u v w : V} (huv huv' : H.Adj u v)
    (p q : H.Walk v w) (hp : (Walk.cons huv p).IsTrail)
    (hq : (Walk.cons huv' q).IsTrail)
    (he : (Walk.cons huv p).edges.toFinset = (Walk.cons huv' q).edges.toFinset) :
    p.edges.toFinset = q.edges.toFinset := by
  have hpnot : s(u, v) ∉ p.edges := (Walk.isTrail_cons huv p).mp hp |>.2
  have hqnot : s(u, v) ∉ q.edges := (Walk.isTrail_cons huv' q).mp hq |>.2
  have h := congrArg (fun S : Finset (Sym2 V) => S.erase s(u, v)) he
  simpa [Walk.edges_cons, hpnot, hqnot] using h

#print axioms Paper7Cycles.trail_tail_edgeFinset_eq

theorem path_eq_of_edgeFinset {u v : V} (p : H.Walk u v) :
    ∀ (q : H.Walk u v), p.IsPath → q.IsPath →
      p.edges.toFinset = q.edges.toFinset → p = q := by
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
        rw [← he]
        simp [Walk.edges_cons]
      have hxy : x = y := by
        simpa only [Walk.snd_cons] using hq.eq_snd_of_mem_edges hxedge
      subst y
      have htail := trail_tail_edgeFinset_eq hux huy p q hp.isTrail hq.isTrail he
      exact congrArg (fun t : H.Walk x v => Walk.cons hux t)
        (ih q hp.of_cons hq.of_cons htail)

#print axioms Paper7Cycles.path_eq_of_edgeFinset

theorem cycle_eq_of_edgeFinset_snd {u : V} {p q : H.Walk u u}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (he : p.edges.toFinset = q.edges.toFinset) (hs : p.snd = q.snd) : p = q := by
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
      have htail := trail_tail_edgeFinset_eq hux huy p q hp.isTrail hq.isTrail he
      exact congrArg (fun t : H.Walk x u => Walk.cons hux t)
        (path_eq_of_edgeFinset p q hpt.1 hqt.1 htail)

#print axioms Paper7Cycles.cycle_eq_of_edgeFinset_snd

end Paper7Cycles
