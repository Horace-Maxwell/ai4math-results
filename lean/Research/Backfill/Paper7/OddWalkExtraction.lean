import Research.Backfill.Paper7.OddWalkReduction

set_option autoImplicit false

namespace Paper7OddWalk

open SimpleGraph

/-- Every odd closed walk contains an odd simple cycle in its edge set, with
length at most the original walk length. This needs no finiteness assumption. -/
theorem exists_odd_cycle_length_le {V : Type*} {H : SimpleGraph V} {u : V}
    (w : H.Walk u u) (hodd : Odd w.length) :
    ∃ (v : V) (c : H.Walk v v),
      c.IsCycle ∧ Odd c.length ∧ c.length ≤ w.length ∧ c.edges ⊆ w.edges := by
  classical
  have aux : ∀ L : ℕ, ∀ (u : V) (p : H.Walk u u), p.length = L → Odd p.length →
      ∃ (v : V) (c : H.Walk v v),
        c.IsCycle ∧ Odd c.length ∧ c.length ≤ p.length ∧ c.edges ⊆ p.edges := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
      intro u p hp hpodd
      by_cases hcycle : p.IsCycle
      · exact ⟨u, p, hcycle, hpodd, le_rfl, fun _ he => he⟩
      · obtain ⟨v, q, hqodd, hqlt, hqedges⟩ :=
          exists_shorter_odd_closedWalk p hpodd hcycle
        obtain ⟨v', c, hc, hcodd, hcle, hcedges⟩ :=
          ih q.length (by omega) v q rfl hqodd
        exact ⟨v', c, hc, hcodd, hcle.trans hqlt.le,
          fun _ he => hqedges (hcedges he)⟩
  exact aux w.length u w rfl hodd

#print axioms Paper7OddWalk.exists_odd_cycle_length_le

end Paper7OddWalk
