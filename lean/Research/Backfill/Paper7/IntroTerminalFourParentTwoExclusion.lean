import Research.Backfill.Paper7.IntroUnicyclicInvisibleFourthMoment
import Research.Backfill.Paper7.IntroTerminalFourParentTwoCycle

/-! Exclude the actual degree-two parent case for a degree-four terminal
in an arbitrary even integral unicyclic graph of order at most 21. The
triangle and two-step collision bounds are proved from the original graph. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix

namespace Paper7IntroTerminalFourParentTwo
open SimpleGraph Matrix BackfillPaper7.Challenge
open Paper7IntroTwoWalkCollision Paper7IntroPendantFour

theorem intro21_even_no_terminal_four_degree_two_parent
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (x p : V) (hxp : G.Adj x p) (hx : G.degree x = 4) (hp : G.degree p = 2)
    (hleaf : ∀ j, G.Adj x j → j ≠ p → G.degree j = 1) : False := by
  have hbound := Paper7IntroFour.intro21_even_spectrum_abs_le_three G b hG hI hn hb
  obtain ⟨c, hcx, hpc, _hrow, _hfactor, hd, hm⟩ :=
    integral_terminal_four_degree_two_parent_moments G hI hbound x p hxp hx hp hleaf
  have htriangle := even_unicyclic_no_triangle G b hG hb
  have hncx : ¬G.Adj c x := by
    intro h
    exact htriangle c p x hpc.symm hxp.symm h.symm
  let E := (G.neighborFinset x).erase p
  have hpN : p ∈ G.neighborFinset x := (G.mem_neighborFinset x p).mpr hxp
  have hEcard : E.card = 3 := by
    rw [Finset.card_erase_of_mem hpN, G.card_neighborFinset_eq_degree, hx]
  have hE : ∀ j ∈ E, j ≠ c ∧ ¬G.Adj c j ∧ ((G.adjMatrix ℝ) ^ 2) c j = 0 := by
    intro j hj
    have hjN := (Finset.mem_erase.mp hj).2
    have hjp := (Finset.mem_erase.mp hj).1
    have hxj : G.Adj x j := (G.mem_neighborFinset x j).mp hjN
    have hdj := hleaf j hxj hjp
    obtain ⟨_a, _hja, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdj
    have hneighbor : ∀ a, G.Adj a j → a = x := by
      intro a haj
      exact (huniq a haj.symm).trans (huniq x hxj.symm).symm
    have hjc : j ≠ c := by
      intro he
      subst j
      exact hncx hxj.symm
    have hncj : ¬G.Adj c j := fun h => hcx (hneighbor c h)
    refine ⟨hjc, hncj, ?_⟩
    have hempty : (G.neighborFinset c).filter (fun a => G.Adj a j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨haN, haj⟩ := Finset.mem_filter.mp ha
      have hca : G.Adj c a := (G.mem_neighborFinset c a).mp haN
      exact hncx ((hneighbor a haj) ▸ hca)
    rw [adjacency_square_common_card, hempty]
    norm_num
  have hcard := unicyclic_fourth_moment_invisible_bound G b hG htriangle c E hE
  rw [hm, hd, hEcard] at hcard
  have hnR : (Fintype.card V : ℝ) ≤ 21 := by exact_mod_cast hn
  norm_num at hcard
  linarith
#print axioms Paper7IntroTerminalFourParentTwo.intro21_even_no_terminal_four_degree_two_parent

end Paper7IntroTerminalFourParentTwo
