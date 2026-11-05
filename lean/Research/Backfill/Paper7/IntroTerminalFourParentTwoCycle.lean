import Research.Backfill.Paper7.IntroTerminalFourParentTwoMoments
import Research.Backfill.Paper7.IntroBridgeVertexFourthMoment
import Research.Backfill.Paper7.IntroEvenRadiusFourExclusion
import Research.Backfill.Paper7.UnicyclicComponentAttachment

/-! An actual degree-two parent of a degree-four terminal must meet the
real cycle at a degree-six vertex in the original even unicyclic order-21
range. The original spectral bound is derived, not added as an assumption.
This necessary local restriction is not a classification theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroTerminalFourParentTwo
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7IntroPendantFour

theorem intro21_even_terminal_four_degree_two_parent_cycle_neighbor
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (x p : V) (hxp : G.Adj x p) (hx : G.degree x = 4) (hp : G.degree p = 2)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) :
    ∃ c : V, c ∈ w.support ∧ c ≠ x ∧ G.Adj p c ∧
      (∀ j, G.Adj p j ↔ j = x ∨ j = c) ∧
      radiusThreeFactor (G.adjMatrix ℝ) *ᵥ Pi.single c 1 = 0 ∧
      G.degree c = 6 ∧ ((G.adjMatrix ℝ) ^ 4) c c = 51 := by
  have hbound := Paper7IntroFour.intro21_even_spectrum_abs_le_three G b hG hI hn hb
  obtain ⟨c, hcx, hpc, hrow, hz, hd, hm⟩ :=
    integral_terminal_four_degree_two_parent_moments G hI hbound x p hxp hx hp hleaf
  have hc : c ∈ w.support := by
    by_contra hnot
    have hbridge : ∀ j, G.Adj c j → G.IsBridge s(c, j) := by
      intro j hcj
      exact Paper7UnicyclicAttachment.unicyclic_off_cycle_edge_isBridge
        G b hG r w hw hlen c j hnot hcj
    have hcard := bridge_vertex_fourth_moment_bound G c hbridge
    rw [hd, hm] at hcard
    have hnR : (Fintype.card V : ℝ) ≤ 21 := by exact_mod_cast hn
    norm_num at hcard
    linarith
  exact ⟨c, hc, hcx, hpc, hrow, hz, hd, hm⟩
#print axioms Paper7IntroTerminalFourParentTwo.intro21_even_terminal_four_degree_two_parent_cycle_neighbor

end Paper7IntroTerminalFourParentTwo
