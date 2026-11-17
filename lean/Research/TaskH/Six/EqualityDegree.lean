import Research.TaskH.Six.DegreeSixComplete
import Research.TaskH.Six.SixNeighborIncidence
import Research.TaskH.Six.SixFiniteBudget

/-!
Actual graph bounds supplied to the later clique and trace arguments. Every
incidence premise is derived here from criticality, S, R and count 420; the
scalar module is used only after these graph transports have been proved.
-/

set_option autoImplicit false

universe u

namespace TaskH.Six

open SimpleGraph _root_.TaskH.Challenge

variable {V : Type u} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem critical_six_card_ge_seven (hcrit : IsCriticalPlus 6 G) :
    7 ≤ Fintype.card V := by
  have h : (7 : ℕ∞) ≤ (Fintype.card V : ℕ∞) := by
    have h := G.chromaticNumber_le_card
    rw [hcrit.1] at h
    exact h
  exact_mod_cast h

theorem noncomplete_degree_ge_seven (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hnot : ¬ IsCompleteOfOrder G 7) (v : V) : 7 ≤ G.degree v := by
  have hd := critical_degree_ge hcrit v
  have hne : G.degree v ≠ 6 := fun he => hnot (degreeSix_isCompleteOfOrder hcrit hs hr v he)
  omega

theorem noncomplete_card_ge_eight (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hnot : ¬ IsCompleteOfOrder G 7) : 8 ≤ Fintype.card V := by
  classical
  have hn := critical_six_card_ge_seven hcrit
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice inferInstance
  have hd := noncomplete_degree_ge_seven hcrit hs hr hnot v
  have hlt := G.degree_lt_card_verts v
  omega

theorem critical_cycleDegree_and_degree_bounds (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V) (hc : modCycleCount 6 G = 420) (v : V) :
    68 ≤ cycleDegree G v ∧ G.degree v ≤ 17 ∧ cycleDegree G v ≤ 420 := by
  have hc61 := critical_sixty_one_le_cycleDegree hcrit hs v
  have havoid := critical_reverse_neighbor_cycle_budget hcrit hs hr hn hc v
  have hforward := critical_forward_neighbor_cycle_budget_sub hcrit hs v
  have hd := degree_le_seventeen_of_avoiding_budget (G.degree v) (cycleDegree G v) hc61 havoid
  have hcycle := cycle_degree_ge_sixty_eight (G.degree v) (cycleDegree G v) hc61 hd hforward
  have hpart := through_add_avoiding (G := G) v
  rw [hc] at hpart
  exact ⟨hcycle, hd, by omega⟩

theorem critical_card_le_thirty_seven (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V) (hc : modCycleCount 6 G = 420) :
    Fintype.card V ≤ 37 := by
  classical
  have hsum : 68 * Fintype.card V ≤ 2520 := by
    calc
      68 * Fintype.card V = ∑ _v : V, 68 := by simp [Nat.mul_comm]
      _ ≤ ∑ v : V, cycleDegree G v := by
        apply Finset.sum_le_sum
        intro v _hv
        exact (critical_cycleDegree_and_degree_bounds hcrit hs hr hn hc v).1
      _ = 2520 := sum_cycleDegree_eq_2520 hs hc
  exact card_le_thirty_seven_of_incidence (Fintype.card V) hsum

theorem critical_degree_ne_seven (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hn : 8 ≤ Fintype.card V) (hc : modCycleCount 6 G = 420) (v : V) :
    G.degree v ≠ 7 := by
  intro hv
  have hsingle := critical_singleton_cycle_bound hcrit hs v
  rw [← cycleDegree_eq_ncard, hv] at hsingle
  norm_num at hsingle
  have havoid := critical_reverse_neighbor_cycle_budget hcrit hs hr hn hc v
  rw [hv] at havoid
  norm_num at havoid
  exact degree_seven_incompatible (cycleDegree G v) hsingle havoid

/-- The high branch has the exact graph bounds used by the finite packing
and trace modules. The internal S/R premises are conclusions of equality. -/
theorem critical_noncomplete_bounds (hcrit : IsCriticalPlus 6 G)
    (hs : ShortSixCycles G) (hr : RainbowSixCycles G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    8 ≤ Fintype.card V ∧ Fintype.card V ≤ 37 ∧
      ∀ v : V, 8 ≤ G.degree v ∧ G.degree v ≤ 17 ∧ 68 ≤ cycleDegree G v := by
  have hn := noncomplete_card_ge_eight hcrit hs hr hnot
  refine ⟨hn, critical_card_le_thirty_seven hcrit hs hr hn hc, ?_⟩
  intro v
  have hd7 := noncomplete_degree_ge_seven hcrit hs hr hnot v
  have hdne := critical_degree_ne_seven hcrit hs hr hn hc v
  have hb := critical_cycleDegree_and_degree_bounds hcrit hs hr hn hc v
  exact ⟨by omega, hb.2.1, hb.1⟩

theorem equality_noncomplete_bounds (hcrit : IsCriticalPlus 6 G)
    (hc : modCycleCount 6 G = 420) (hnot : ¬ IsCompleteOfOrder G 7) :
    8 ≤ Fintype.card V ∧ Fintype.card V ≤ 37 ∧
      ∀ v : V, 8 ≤ G.degree v ∧ G.degree v ≤ 17 ∧ 68 ≤ cycleDegree G v :=
  critical_noncomplete_bounds hcrit (equality_shortSixCycles hcrit hc)
    (equality_rainbowSixCycles hcrit hc) hc hnot

end TaskH.Six

#print axioms TaskH.Six.critical_six_card_ge_seven
#print axioms TaskH.Six.noncomplete_degree_ge_seven
#print axioms TaskH.Six.noncomplete_card_ge_eight
#print axioms TaskH.Six.critical_cycleDegree_and_degree_bounds
#print axioms TaskH.Six.critical_card_le_thirty_seven
#print axioms TaskH.Six.critical_degree_ne_seven
#print axioms TaskH.Six.critical_noncomplete_bounds
#print axioms TaskH.Six.equality_noncomplete_bounds
