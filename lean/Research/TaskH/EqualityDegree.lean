import Research.TaskH.EqualityShortCycles
import Research.TaskH.CycleIncidence
import Research.TaskH.FourCount

/-!
The high-minimum-degree branch is excluded using only the original critical
and equality hypotheses. All intermediate short-cycle and order bounds are
conclusions of the preceding actual-graph transports.
-/

set_option autoImplicit false

universe u

namespace TaskH

open Challenge SimpleGraph

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

theorem critical_four_card_ge_five (hcrit : IsCriticalPlus 4 G) :
    5 ≤ Fintype.card V := by
  have h : (5 : ℕ∞) ≤ (Fintype.card V : ℕ∞) := by
    have h := G.chromaticNumber_le_card
    rw [hcrit.1] at h
    exact h
  exact_mod_cast h

/-- The actual critical equality graph has a vertex of degree exactly four. -/
theorem equality_exists_degree_four [DecidableRel G.Adj]
    (hcrit : IsCriticalPlus 4 G) (hcount : modCycleCount 4 G = 15) :
    ∃ v : V, G.degree v = 4 := by
  classical
  have hshort : ShortFourCycles G := equality_shortFourCycles hcrit hcount
  have hn15 := card_le_fifteen_of_short_critical_count hcrit hshort hcount
  have hn5 := critical_four_card_ge_five hcrit
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice inferInstance
  by_contra hnot
  have hdeg : ∀ x : V, 5 ≤ G.degree x := by
    intro x
    have hge := critical_degree_ge hcrit x
    have hne : G.degree x ≠ 4 := by
      intro he
      exact hnot ⟨x, he⟩
    omega
  have hn6 : 6 ≤ Fintype.card V := by
    have hlt := G.degree_lt_card_verts v
    have hge := hdeg v
    omega
  exact FourCount.not_fifteen_cycles_of_minDegree_five G hdeg hn6 hn15 hcount

end TaskH

#print axioms TaskH.critical_four_card_ge_five
#print axioms TaskH.equality_exists_degree_four
