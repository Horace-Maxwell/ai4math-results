import Mathlib

set_option autoImplicit false

namespace Paper7OddWalk

open SimpleGraph

/-- An odd closed walk in a simple graph has at least three edges. -/
theorem three_le_length_of_odd {V : Type*} {H : SimpleGraph V} {u : V}
    (w : H.Walk u u) (hodd : Odd w.length) : 3 ≤ w.length := by
  have hne : w.length ≠ 1 := by
    intro h
    exact (Walk.adj_of_length_eq_one (p := w) h).ne rfl
  have hmod := Nat.odd_iff.mp hodd
  omega

#print axioms Paper7OddWalk.three_le_length_of_odd

/-- If an odd closed walk is not a cycle, a strictly shorter odd closed walk
can be obtained without introducing any new edge. -/
theorem exists_shorter_odd_closedWalk {V : Type*} {H : SimpleGraph V} {u : V}
    (w : H.Walk u u) (hodd : Odd w.length) (hnot : ¬ w.IsCycle) :
    ∃ (v : V) (q : H.Walk v v),
      Odd q.length ∧ q.length < w.length ∧ q.edges ⊆ w.edges := by
  classical
  have hthree := three_le_length_of_odd w hodd
  have hnil : ¬ w.Nil := by
    intro h
    have hzero := h.length_eq_zero
    omega
  have htail : ¬ w.tail.IsPath := by
    intro hpath
    exact hnot (Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨hpath, hthree⟩)
  rw [Walk.isPath_iff_isSubwalk_imp_nil] at htail
  push Not at htail
  obtain ⟨v, c, hcsub, hcnil⟩ := htail
  obtain ⟨a, b, hab⟩ := hcsub
  have hw : w = Walk.cons (w.adj_snd hnil) ((a.append c).append b) :=
    (w.cons_tail_eq hnil).symm.trans (congrArg (Walk.cons (w.adj_snd hnil)) hab)
  have hlen : w.length = a.length + c.length + b.length + 1 := by
    simpa only [Walk.length_cons, Walk.length_append] using congrArg Walk.length hw
  have hcpos : 0 < c.length := Walk.not_nil_iff_lt_length.mp hcnil
  have hc_edges : c.edges ⊆ w.edges := by
    intro e he
    rw [hw]
    simp only [Walk.edges_cons, Walk.edges_append, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (Or.inr he))
  by_cases hcodd : Odd c.length
  · exact ⟨v, c, hcodd, by omega, hc_edges⟩
  · let r : H.Walk u u := Walk.cons (w.adj_snd hnil) (a.append b)
    have hrlen : r.length = a.length + b.length + 1 := by
      simp only [r, Walk.length_cons, Walk.length_append]
    have hrodd : Odd r.length := by
      have hwmod := Nat.odd_iff.mp hodd
      have hcmod := Nat.not_odd_iff.mp hcodd
      apply Nat.odd_iff.mpr
      omega
    have hr_edges : r.edges ⊆ w.edges := by
      intro e he
      change e ∈ (Walk.cons (w.adj_snd hnil) (a.append b)).edges at he
      rw [hw]
      simp only [Walk.edges_cons, Walk.edges_append, List.mem_cons, List.mem_append] at he ⊢
      tauto
    exact ⟨u, r, hrodd, by omega, hr_edges⟩

#print axioms Paper7OddWalk.exists_shorter_odd_closedWalk

end Paper7OddWalk
