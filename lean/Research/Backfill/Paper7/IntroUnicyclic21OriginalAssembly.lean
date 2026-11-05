import Research.Backfill.Paper7.IntroThreeLeafDegreeThreeOriginalExclusion
import Research.Backfill.Paper7.IntroThreeLeafFourOriginalExclusion
import Research.Backfill.Paper7.IntroEvenDegreeTwoSixGraphs
import Research.Backfill.Paper7.IntroAttachmentLeafStarShape
import Research.Backfill.Paper7.IntroAttachmentZeroOneThree
import Research.Backfill.Paper7.UnicyclicComponentAttachment
import Research.Backfill.Paper7.IntroOddOrderThree
import Research.Backfill.Paper7.ControlB4Representatives
import Research.Backfill.Paper7.BareCycleIntegralClassification
import Research.Backfill.Paper7.DihedralBudgetIntegral

/-! Original degree bound and exact frozen IntroUnicyclic21 candidate.
The degree-three exclusion and conditional classifier remain pending parents.
No outside-degree, Sun representation or spectral premise is added to the target. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroOriginalAssembly
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra

theorem intro21_even_off_cycle_degree_le_two
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b) :
    ∀ x, x ∉ w.support → G.degree x ≤ 2 := by
  intro x hx
  let xo : {q : V // q ∉ w.support} := ⟨x, hx⟩
  let H := deleteVertices G {q | q ∈ w.support}
  let C := H.connectedComponentMk xo
  let q : C.supp := ⟨xo, ConnectedComponent.connectedComponentMk_mem⟩
  obtain ⟨ao, c, hao, hac, _huniq, _hreach⟩ :=
    Paper7UnicyclicAttachment.unicyclic_component_attachment_data
      G b hG r w hw hlen C
  let a : C.supp := ⟨ao, hao⟩
  obtain ⟨Y, hY, hdegree, _hne, _hinj, hdata, hcover, _hNa, _hNl⟩ :=
    Paper7IntroAttachmentLeafStar.intro21_even_actual_attachment_leaf_star
      G b hG hI hn hb r w hw hlen C a c hac
  have hcases := Paper7IntroZeroOneThree.intro21_even_attachment_zero_one_three
    G b hG hI hn hb r w hw hlen C a c hac
  change ((G.neighborFinset a.val.val).erase c.val).card = 0 ∨
    ((G.neighborFinset a.val.val).erase c.val).card = 1 ∨
    (((G.neighborFinset a.val.val).erase c.val).card = 3 ∧
      (G.degree c.val = 3 ∨ G.degree c.val = 4)) at hcases
  have hYsmall : Y.card = 0 ∨ Y.card = 1 := by
    rcases hcases with h0 | h1 | hthree
    · left
      rw [hY]
      exact h0
    · right
      rw [hY]
      exact h1
    · obtain ⟨h3, hdegree_cases⟩ := hthree
      rcases hdegree_cases with hd3 | hd4
      · exact (Paper7IntroThreeThreeExclusion.intro21_even_not_three_leaf_degree_three
          G b hG hI hn hb r w hw hlen C a c hac h3 hd3).elim
      · exact (Paper7IntroThreeFourExclusion.intro21_even_not_three_leaf_degree_four
          G b hG hI hn hb r w hw hlen C a c hac h3 hd4).elim
  have ha2 : G.degree a.val.val ≤ 2 := by
    rcases hYsmall with h0 | h1 <;> omega
  rcases hcover q with hqa | hleaf
  · have hxa : x = a.val.val := congrArg (fun t : C.supp => t.val.val) hqa
    rw [hxa]
    exact ha2
  · obtain ⟨i, hqi⟩ := hleaf
    have hxi : x = i.val := hqi
    have hi : G.degree i.val = 1 := (hdata i).2.1
    rw [hxi, hi]
    omega
#print axioms Paper7IntroOriginalAssembly.intro21_even_off_cycle_degree_le_two

theorem check_IntroUnicyclic21 : BackfillPaper7.Challenge.IntroUnicyclic21 := by
  intro V _ _ G _ hn hU
  constructor
  · intro hI
    obtain ⟨b, hG⟩ := hU
    rcases Nat.even_or_odd b with hb | hb
    · obtain ⟨_s, ⟨r, w, hw, hlen, _hedges⟩, _hunique⟩ := hG.2
      have hdeg := intro21_even_off_cycle_degree_le_two G b hG hI hn hb r w hw hlen
      exact Paper7IntroDegreeTwoClassification.intro21_even_off_cycle_degree_two_six_graphs
        G b hG hI hn hb r w hw hlen hdeg
    · exact Or.inl (Paper7IntroOddMultiplicity.intro21_odd_iso_cycle_three
        G b hG hI hn hb)
  · intro hSix
    rcases hSix with h3 | h4 | h6 | h13 | h20a | h20b
    · obtain ⟨e⟩ := h3
      exact (Paper7PruningCanonical.integral_graphIso_iff G (cycleGraph 3) e).mp
        Paper7BareCycle.cycleGraph_three_integral
    · obtain ⟨e⟩ := h4
      exact (Paper7PruningCanonical.integral_graphIso_iff G (cycleGraph 4) e).mp
        Paper7BareCycle.cycleGraph_four_integral
    · obtain ⟨e⟩ := h6
      exact (Paper7PruningCanonical.integral_graphIso_iff G (cycleGraph 6) e).mp
        Paper7BareCycle.cycleGraph_six_integral
    · obtain ⟨e⟩ := h13
      exact (Paper7PruningCanonical.integral_graphIso_iff G (sunGraph 4 G13) e).mp
        Paper7ControlB4.g13_integral
    · obtain ⟨e⟩ := h20a
      exact (Paper7PruningCanonical.integral_graphIso_iff G (sunGraph 4 G20a) e).mp
        Paper7ControlB4.g20a_integral
    · obtain ⟨e⟩ := h20b
      exact (Paper7PruningCanonical.integral_graphIso_iff G (sunGraph 4 G20b) e).mp
        Paper7ControlB4.g20b_integral
#print axioms Paper7IntroOriginalAssembly.check_IntroUnicyclic21

end Paper7IntroOriginalAssembly
