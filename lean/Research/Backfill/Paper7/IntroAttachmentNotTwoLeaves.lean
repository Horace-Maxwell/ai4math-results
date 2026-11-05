import Research.Backfill.Paper7.IntroAttachmentLeafStarWeights
import Research.Backfill.Paper7.IntroTerminalLeafPair

/-! Exclude two canonical leaves at an actual deleted-cycle attachment.
All leaf and spectral-count information is obtained from the original graph
inside the proof. Cardinality two is only the contradiction branch. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroAttachmentLeafStar
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroLeafStarWeights Paper7IntroLocalQuartic

theorem intro21_even_attachment_leaf_card_ne_two
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val) :
    ((G.neighborFinset a.val.val).erase c.val).card ≠ 2 := by
  intro htwo
  have hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨Y, _i₀, _eps, _f, hY, _hpos, _hseven, _hnine, hdeg, _hca,
    _hinj, hdata, _hcover, _hNa, _hNl, hthree, _rest⟩ :=
    intro21_even_actual_leaf_star_perron_weights G b hG hI hn hb r w hw hlen C a c hac hleaves
  have hdeg3 : G.degree a.val.val = 3 := by
    rw [hY, htwo] at hdeg
    omega
  have hleaf : ∀ j, G.Adj a.val.val j → j ≠ c.val → G.degree j = 1 := by
    intro j haj hjc
    have hjY : j ∈ Y := by
      rw [hY]
      exact Finset.mem_erase.mpr ⟨hjc, (G.mem_neighborFinset a.val.val j).mpr haj⟩
    exact (hdata ⟨j, hjY⟩).2.1
  have hdeg2 := (integral_radius_three_small_terminal_fan_degree_two
    G hG.1 hI hthree a.val.val c.val hac (by omega) (by omega) hleaf).1
  omega
#print axioms Paper7IntroAttachmentLeafStar.intro21_even_attachment_leaf_card_ne_two

end Paper7IntroAttachmentLeafStar
