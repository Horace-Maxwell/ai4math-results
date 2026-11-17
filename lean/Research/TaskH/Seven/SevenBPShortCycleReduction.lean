import Research.TaskH.Seven.SevenBPExternalCapacity
import Research.TaskH.Seven.SevenBPCycleWitness

/-! The actual shortest long cycle has length below twenty at order at most49.
Every internal/external capacity used here was derived on the original graph
in the imported sources. No capacity or coverage premise is assumed. -/

set_option autoImplicit false

universe u

namespace TaskH.Seven.BP

open SimpleGraph
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem shortest_long_cycle_length_lt_twenty (hb : G.IsBipartite)
    (hn : Fintype.card V ≤ 49) (hd : ∀ x : V, 7 ≤ G.degree x) {a : V}
    (p : G.Walk a a) (hp : ShortestLongCycle p) : p.length < 20 := by
  by_contra hnot
  have h20 : 20 ≤ p.length := by omega
  have ho := shortest_external_capacity hb p hp h20
  have hdS : ∀ x ∈ cycleSupport p, 7 ≤ G.degree x := fun x _ => hd x
  have heven := Nat.even_iff.mp (closed_walk_even hb p)
  have hcases : p.length = 20 ∨ p.length = 22 ∨ 24 ≤ p.length := by omega
  rcases hcases with hL | hL | hL
  · exact boundary_twenty_impossible (cycleSupport p) hn
      (by simpa only [cycleSupport_card p hp.1] using hL) hdS
      (shortest_internal_capacity_twenty hb p hp hL) ho
  · exact boundary_twenty_two_impossible (cycleSupport p) hn
      (by simpa only [cycleSupport_card p hp.1] using hL) hdS
      (shortest_internal_capacity_twenty_two hb p hp hL) ho
  · exact boundary_at_least_twenty_four_impossible (cycleSupport p) hn
      (by simpa only [cycleSupport_card p hp.1] using hL) hdS
      (shortest_internal_capacity_at_least_twenty_four hb p hp hL) ho

theorem shortest_long_cycle_sixteen_or_eighteen (hb : G.IsBipartite)
    (hn : Fintype.card V ≤ 49) (hd : ∀ x : V, 7 ≤ G.degree x)
    (h14 : NoFourteenCycle G) {a : V} (p : G.Walk a a)
    (hp : ShortestLongCycle p) : p.length = 16 ∨ p.length = 18 := by
  have hlt := shortest_long_cycle_length_lt_twenty hb hn hd p hp
  have heven := Nat.even_iff.mp (closed_walk_even hb p)
  have hne := h14 p hp.1
  have hlong := hp.2.1
  omega

theorem exists_cycle_sixteen_or_eighteen [Nonempty V] (hb : G.IsBipartite)
    (hn : Fintype.card V ≤ 49) (hd : ∀ x : V, 7 ≤ G.degree x)
    (h14 : NoFourteenCycle G) :
    ∃ (a : V) (p : G.Walk a a), p.IsCycle ∧ (p.length = 16 ∨ p.length = 18) := by
  obtain ⟨a, p, hp⟩ := exists_shortest_long_cycle hb hd
  exact ⟨a, p, hp.1, shortest_long_cycle_sixteen_or_eighteen hb hn hd h14 p hp⟩

end TaskH.Seven.BP

#print axioms TaskH.Seven.BP.shortest_long_cycle_length_lt_twenty
#print axioms TaskH.Seven.BP.shortest_long_cycle_sixteen_or_eighteen
#print axioms TaskH.Seven.BP.exists_cycle_sixteen_or_eighteen
