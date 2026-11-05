import Research.Backfill.Paper7.IntroTerminalFourParentQuartic
import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment
import Research.Backfill.Paper7.UnicyclicComponentAttachment

/-! The bridge premise is derived for every actual off-cycle parent.
The terminal condition remains an explicit local condition, not an Intro21 premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroTerminalFourParent
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroLocalQuartic
open Paper7IntroPendantFour Paper7UnicyclicAttachment

theorem integral_degree_four_terminal_bridge_parent_order_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hI : IsIntegralGraph G)
    (x p : V) (hxp : G.Adj x p) (hx : G.degree x = 4)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1)
    (hbridge : ∀ j, G.Adj p j → G.IsBridge s(p, j)) :
    2 * (G.degree p : ℝ) ^ 2 - 6 * (G.degree p : ℝ) + 9 ≤ Fintype.card V := by
  have hq := integral_degree_four_terminal_parent_quartic_bound G hI x p hxp hx hleaf
  have hf := bridge_vertex_fourth_moment_bound G p hbridge
  change 3 * ((G.degree p : ℝ) - 2) ^ 2 ≤
    ((G.adjMatrix ℝ) ^ 4) p p - 5 * ((G.adjMatrix ℝ) ^ 2) p p +
      4 * (1 : Matrix V V ℝ) p p at hq
  rw [pow_two (G.adjMatrix ℝ), G.adjMatrix_mul_self_apply_self, Matrix.one_apply_eq] at hq
  nlinarith
#print axioms Paper7IntroTerminalFourParent.integral_degree_four_terminal_bridge_parent_order_bound

theorem intro21_degree_four_terminal_off_cycle_parent_le_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (x p : V) (hp : p ∉ w.support) (hxp : G.Adj x p) (hx : G.degree x = 4)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) : G.degree p ≤ 4 := by
  have hbridge : ∀ j, G.Adj p j → G.IsBridge s(p, j) := by
    intro j hpj
    exact unicyclic_off_cycle_edge_isBridge G b hG r w hw hlen p j hp hpj
  have hlower := integral_degree_four_terminal_bridge_parent_order_bound
    G hI x p hxp hx hleaf hbridge
  have hnR : (Fintype.card V : ℝ) ≤ 21 := by exact_mod_cast hn
  by_contra hno
  have hp5 : 5 ≤ G.degree p := by omega
  have hp5R : (5 : ℝ) ≤ (G.degree p : ℝ) := by exact_mod_cast hp5
  nlinarith [sq_nonneg ((G.degree p : ℝ) - 5)]
#print axioms Paper7IntroTerminalFourParent.intro21_degree_four_terminal_off_cycle_parent_le_four

end Paper7IntroTerminalFourParent
