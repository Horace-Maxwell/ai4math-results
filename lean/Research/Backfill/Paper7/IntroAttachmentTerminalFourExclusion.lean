import Research.Backfill.Paper7.IntroTerminalFourParentLeafInterface
import Research.Backfill.Paper7.IntroTerminalFourParentDegreeRelation
import Research.Backfill.Paper7.IntroTerminalFourParentTwoExclusion

/-! Exclusion of an actual degree-four terminal adjacent to the attachment
of its actual outside component. This does not quantify over terminals at
the attachment itself and is not a full Intro21 classification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroTerminalFourRemote
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroFour Paper7IntroTerminalFourParent Paper7IntroTerminalFourParentTwo

theorem intro21_even_no_attachment_adjacent_terminal_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : G.Adj x.val.val a.val.val) (hx : G.degree x.val.val = 4)
    (hxleaf : ∀ j, G.Adj x.val.val j → j ≠ a.val.val → G.degree j = 1) : False := by
  have hxc : x.val.val ≠ c.val := by
    intro he
    exact x.val.property (he.symm ▸ c.property)
  have hxN : x.val.val ∈ G.neighborFinset a.val.val :=
    (G.mem_neighborFinset a.val.val x.val.val).mpr hxa.symm
  have hcN : c.val ∈ (G.neighborFinset a.val.val).erase x.val.val :=
    Finset.mem_erase.mpr ⟨hxc.symm, (G.mem_neighborFinset a.val.val c.val).mpr hac⟩
  have ha2 : 2 ≤ G.degree a.val.val := by
    have hpos := Finset.card_pos.mpr ⟨c.val, hcN⟩
    rw [Finset.card_erase_of_mem hxN, G.card_neighborFinset_eq_degree] at hpos
    omega
  have ha4 := intro21_degree_four_terminal_off_cycle_parent_le_four
    G b hG hI hn r w hw hlen x.val.val a.val.val a.val.property hxa hx hxleaf
  have haNe2 : G.degree a.val.val ≠ 2 := by
    intro ha
    exact intro21_even_no_terminal_four_degree_two_parent
      G b hG hI hn hb x.val.val a.val.val hxa hx ha hxleaf
  have ha34 : G.degree a.val.val = 3 ∨ G.degree a.val.val = 4 := by omega
  have hbound := intro21_even_spectrum_abs_le_three G b hG hI hn hb
  have hpleaf := intro21_even_attachment_terminal_four_other_neighbors_leaves
    G b hG hI hn hb r w hw hlen C a c hac x hxa hx hxleaf
  have hdegree := integral_terminal_four_parent_other_degree_relation
    G hI hbound x.val.val a.val.val c.val hxa hac hxc hx hxleaf hpleaf
  have hcap : ∀ t ∈ spec G, t ≤ (3 : ℝ) := by
    intro t ht
    exact (le_abs_self t).trans (hbound t ht)
  have hc9 := unicyclic_degree_lt_spectral_bound_sq G b hG 3 (by norm_num) hcap c.val
  norm_num at hc9
  have hc9R : (G.degree c.val : ℝ) < 9 := by exact_mod_cast hc9
  rcases ha34 with ha | ha
  · rw [ha] at hdegree
    norm_num at hdegree
    linarith
  · rw [ha] at hdegree
    norm_num at hdegree
    linarith
#print axioms Paper7IntroTerminalFourRemote.intro21_even_no_attachment_adjacent_terminal_four

end Paper7IntroTerminalFourRemote
