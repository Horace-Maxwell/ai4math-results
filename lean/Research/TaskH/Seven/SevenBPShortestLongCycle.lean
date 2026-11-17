import Research.TaskH.Seven.SevenBPLongCycle

/-! A shortest actual long cycle and the two actual cycles cut out by a chord.
These are graph constructions, not supplied chord-capacity assumptions. The
external two-ear bound and all C18/C16 attachment budgets remain separate. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical

variable {V : Type u} {G : SimpleGraph V}

def ShortestLongCycle {a : V} (p : G.Walk a a) : Prop :=
  p.IsCycle ∧ 14 ≤ p.length ∧ ∀ (b : V) (q : G.Walk b b),
    q.IsCycle → 14 ≤ q.length → p.length ≤ q.length

theorem exists_shortest_long_cycle [Fintype V] [Nonempty V]
    (hb : G.IsBipartite) (hd : ∀ a : V, 7 ≤ G.degree a) :
    ∃ (a : V) (p : G.Walk a a), ShortestLongCycle p := by
  classical
  let P : ℕ → Prop := fun n => ∃ (a : V) (p : G.Walk a a),
    p.IsCycle ∧ 14 ≤ n ∧ p.length = n
  have hP : ∃ n : ℕ, P n := by
    obtain ⟨a, p, hp, hl⟩ := exists_cycle_length_ge_fourteen hb hd
    exact ⟨p.length, a, p, hp, hl, rfl⟩
  obtain ⟨a, p, hp, hl, he⟩ := Nat.find_spec hP
  refine ⟨a, p, hp, ?_, ?_⟩
  · omega
  · intro b q hq hq14
    have hm := Nat.find_min' hP (show P q.length from ⟨b, q, hq, hq14, rfl⟩)
    omega

theorem closed_walk_even (hb : G.IsBipartite) {a : V} (p : G.Walk a a) :
    Even p.length := by
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv hb.some
  exact (c.even_length_iff_congr p).mpr Iff.rfl

theorem shorter_cycle_le_twelve (hb : G.IsBipartite) {a b : V}
    (p : G.Walk a a) (hshort : ShortestLongCycle p)
    (q : G.Walk b b) (hq : q.IsCycle) (hlt : q.length < p.length) :
    q.length ≤ 12 := by
  have hlt14 : q.length < 14 := by
    by_contra hn
    have hm := hshort.2.2 b q hq (by omega)
    omega
  obtain ⟨k, hk⟩ := closed_walk_even hb q
  omega

theorem shortest_cycle_chord_distances (hb : G.IsBipartite) {a : V}
    (p : G.Walk a a) (hshort : ShortestLongCycle p)
    (n : ℕ) (hn : 2 ≤ n) (hfar : n + 2 ≤ p.length)
    (ha : G.Adj a (p.getVert n)) : n ≤ 11 ∧ p.length - n ≤ 11 := by
  have htake : (p.take n).length = n := by
    simp only [Walk.take_length, inf_eq_left.mpr (by omega : n ≤ p.length)]
  have hdrop : (p.drop n).length = p.length - n := by
    simp only [Walk.drop_length]
  have hfirst : (Walk.cons ha.symm (p.take n)).IsCycle :=
    path_closing_cycle (p.take n) (hshort.1.isPath_take (by omega)) ha (by omega)
  have hsecond : (Walk.cons ha (p.drop n)).IsCycle :=
    path_closing_cycle (p.drop n) (hshort.1.isPath_drop (by omega)) ha.symm (by omega)
  have hlen1 : (Walk.cons ha.symm (p.take n)).length = n + 1 := by
    simp only [Walk.length_cons, htake]
  have hlen2 : (Walk.cons ha (p.drop n)).length = p.length - n + 1 := by
    simp only [Walk.length_cons, hdrop]
  have h1 := shorter_cycle_le_twelve hb p hshort _ hfirst (by omega)
  have h2 := shorter_cycle_le_twelve hb p hshort _ hsecond (by omega)
  omega

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.ShortestLongCycle
#print axioms TaskH.Seven.BP.exists_shortest_long_cycle
#print axioms TaskH.Seven.BP.closed_walk_even
#print axioms TaskH.Seven.BP.shorter_cycle_le_twelve
#print axioms TaskH.Seven.BP.shortest_cycle_chord_distances
