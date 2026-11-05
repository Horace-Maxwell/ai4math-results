import Research.Backfill.Paper7.IntroAttachmentLeafDegreeCandidates
import Research.Backfill.Paper7.IntroAttachmentFiveSevenExclusion
import Research.Backfill.Paper7.IntroFourLeafDegreeSixExclusion

/-! Combine the original necessary alternatives with the two developed
exclusions. No candidate table or leaf shape is added as a premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroZeroOneThree
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroLeafDegreeCandidates Paper7IntroHalfNorm Paper7IntroFourLeafExclusion

theorem intro21_even_attachment_zero_one_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val) :
    let m := ((G.neighborFinset a.val.val).erase c.val).card
    let d := G.degree c.val
    m = 0 ∨ m = 1 ∨ (m = 3 ∧ (d = 3 ∨ d = 4)) := by
  have hcases := intro21_even_attachment_leaf_degree_candidates
    G b hG hI hn hb r w hw hlen C a c hac
  have h57 := intro21_even_attachment_not_five_seven_or_seven_five
    G b hG hI hn hb r w hw hlen C a c hac
  have h46 := intro21_even_attachment_not_four_leaves_degree_six
    G b hG hI hn hb r w hw hlen C a c hac
  rcases hcases with h0 | h1 | h3 | h4 | h5 | h7
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h3)
  · exact (h46 h4).elim
  · exact (h57.1 h5).elim
  · exact (h57.2 h7).elim
#print axioms Paper7IntroZeroOneThree.intro21_even_attachment_zero_one_three

end Paper7IntroZeroOneThree
