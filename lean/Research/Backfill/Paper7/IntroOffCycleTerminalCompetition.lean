import Research.Backfill.Paper7.IntroTerminalFanCompetition
import Research.Backfill.Paper7.IntroOffCycleNonleafDepth

/-! The degree bound is derived from the original graph assumptions. Terminal
conditions remain explicit in this local uniqueness helper, not in Intro21. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroTerminalCompetition
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra Paper7IntroTreeDepth

theorem intro21_even_attachment_degree_four_terminal_unique
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x y : C.supp) (hxa : G.Adj x.val.val a.val.val) (hya : G.Adj y.val.val a.val.val)
    (hx : G.degree x.val.val = 4) (hy : 2 ≤ G.degree y.val.val)
    (hxleaf : ∀ j, G.Adj x.val.val j → j ≠ a.val.val → G.degree j = 1)
    (hyleaf : ∀ j, G.Adj y.val.val j → j ≠ a.val.val → G.degree j = 1) : x = y := by
  have hyne : y ≠ a := by
    intro he
    subst y
    exact G.irrefl hya
  have hy4 := (intro21_even_component_degree_four_only_next_to_attachment
    G b hG hI hn hb r w hw hlen C a c hac y hyne).1
  have he := integral_degree_four_terminal_unique_small_terminal_sibling
    G hI x.val.val y.val.val a.val.val hxa hya hx hy (by omega) hxleaf hyleaf
  exact Subtype.ext (Subtype.ext he)
#print axioms Paper7IntroTerminalCompetition.intro21_even_attachment_degree_four_terminal_unique

end Paper7IntroTerminalCompetition
