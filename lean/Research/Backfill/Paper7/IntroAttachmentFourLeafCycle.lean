import Research.Backfill.Paper7.IntroFourthExcessFourCycle
import Research.Backfill.Paper7.IntroPureLeafStarCycleFourthConstraint

/-! The original four-leaf/six-degree branch forces the actual unique cycle
to be a four-cycle. The four vertices and full support are conclusions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroFourCycleBridge
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroPureLeafConstraints Paper7IntroTwoWalkCollision

theorem intro21_even_four_leaf_degree_six_cycle
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {z | z ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {z : V // z ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm4 : ((G.neighborFinset a.val.val).erase c.val).card = 4)
    (hd6 : G.degree c.val = 6) :
    b = 4 ∧ ∃ p j q : V,
      c.val ≠ p ∧ c.val ≠ j ∧ c.val ≠ q ∧ p ≠ j ∧ p ≠ q ∧ j ≠ q ∧
      G.Adj c.val p ∧ G.Adj p j ∧ G.Adj j q ∧ G.Adj q c.val ∧
      (∀ z : V, z ∈ w.support ↔ z = c.val ∨ z = p ∨ z = j ∨ z = q) ∧
      (∀ t : V, (G.Adj c.val t ∧ G.Adj t j) ↔ t = p ∨ t = q) := by
  have hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty :=
    Finset.card_pos.mp (by rw [hm4]; norm_num)
  obtain ⟨Y, _l, hY, _hl, _hdeg, _hne, _hinj, _hdata, _hcover, _hNa, _hNl, hM⟩ :=
    intro21_even_actual_leaf_star_cycle_fourth_constraint
      G b hG hI hn hb r w hw hlen C a c hac hleaves
  have hY4 : Y.card = 4 := by rw [hY]; exact hm4
  have hmoment : ((G.adjMatrix ℝ) ^ 4) c.val c.val = 51 := by
    rw [hY4, hd6] at hM
    norm_num at hM
    exact hM
  have hlarge : (G.degree c.val : ℝ) ^ 2 + Fintype.card V - (G.degree c.val : ℝ) - 1 <
      ((G.adjMatrix ℝ) ^ 4) c.val c.val := by
    rw [hd6, hmoment]
    have hnR : (Fintype.card V : ℝ) ≤ 21 := by exact_mod_cast hn
    norm_num
    linarith
  exact unicyclic_fourth_excess_forces_four_cycle
    G b hG (even_unicyclic_no_triangle G b hG hb) r w hw hlen c.val hlarge
#print axioms Paper7IntroFourCycleBridge.intro21_even_four_leaf_degree_six_cycle

end Paper7IntroFourCycleBridge
