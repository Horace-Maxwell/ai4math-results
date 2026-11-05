import Research.Backfill.Paper7.IntroDeletedThreeNeighborTransfer
import Research.Backfill.Paper7.IntroOutsideDepthThreeLeaf
import Research.Backfill.Paper7.IntroAttachmentTerminalFourExclusion
import Research.Backfill.Paper7.IntroMixedPendantArmExclusion

/-! Under the original even integral unicyclic order bound, every vertex
of an actual outside component other than its attachment has degree at most
three. Actual leaf and depth facts are derived, not classification premises. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroNonattachmentFour
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7UnicyclicAttachment Paper7IntroTerminalFourRemote Paper7IntroTreeDepth
open Paper7IntroMixedArms

theorem intro21_even_no_nonattachment_degree_four
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxaNe : x ≠ a) (hx : G.degree x.val.val = 4) : False := by
  have hxa := (intro21_even_component_degree_four_only_next_to_attachment
    G b hG hI hn hb r w hw hlen C a c hac x hxaNe).2 (by omega)
  by_cases hterminal : ∀ j, G.Adj x.val.val j → j ≠ a.val.val → G.degree j = 1
  · exact intro21_even_no_attachment_adjacent_terminal_four
      G b hG hI hn hb r w hw hlen C a c hac x hxa hx hterminal
  · obtain ⟨⟨k, hxk, hk, _hka⟩, hchild⟩ :=
      intro21_even_attachment_degree_four_neighbor_structure
        G b hG hI hn hb r w hw hlen C a c hac x hxa hx
    push Not at hterminal
    obtain ⟨yv, hxyv, hyva, hyv1⟩ := hterminal
    have hyv2 : G.degree yv = 2 := by
      have hle := hchild yv hxyv hyva
      have hp := hxyv.degree_pos_right
      omega
    obtain ⟨_pair, _hpair, huniq⟩ :=
      unicyclic_component_attachment_endpoints G b hG r w hw hlen C
    have hgate : ∀ (v : {q : V // q ∉ w.support}), v ∈ C.supp →
        ∀ t : {q : V // q ∈ w.support}, G.Adj v.val t.val → v = a.val := by
      intro v hv t hvt
      exact congrArg Prod.fst ((huniq (v, t) ⟨hv, hvt⟩).trans
        (huniq (a.val, c) ⟨a.property, hac⟩).symm)
    have hyS : yv ∉ w.support := by
      intro hyS
      exact hxaNe (Subtype.ext (hgate x.val x.property ⟨yv, hyS⟩ hxyv))
    let yo : {q : V // q ∉ w.support} := ⟨yv, hyS⟩
    have hyC : yo ∈ C.supp := C.mem_supp_of_adj_mem_supp x.property hxyv
    let y : C.supp := ⟨yo, hyC⟩
    have hya : y ≠ a := by
      intro he
      exact hyva (congrArg (fun u : C.supp => u.val.val) he)
    have hxmem : x.val.val ∈ G.neighborFinset yv :=
      (G.mem_neighborFinset yv x.val.val).mpr hxyv.symm
    obtain ⟨lv, hlv⟩ : ((G.neighborFinset yv).erase x.val.val).Nonempty := by
      apply Finset.card_pos.mp
      have hc := Finset.card_erase_add_one hxmem
      rw [G.card_neighborFinset_eq_degree, hyv2] at hc
      omega
    have hlvx : lv ≠ x.val.val := (Finset.mem_erase.mp hlv).1
    have hyvL : G.Adj yv lv :=
      (G.mem_neighborFinset yv lv).mp (Finset.mem_erase.mp hlv).2
    have hlS : lv ∉ w.support := by
      intro hlS
      exact hya (Subtype.ext (hgate y.val y.property ⟨lv, hlS⟩ hyvL))
    let lo : {q : V // q ∉ w.support} := ⟨lv, hlS⟩
    have hlC : lo ∈ C.supp := C.mem_supp_of_adj_mem_supp y.property hyvL
    let l : C.supp := ⟨lo, hlC⟩
    have hlx : l ≠ x := by
      intro he
      exact hlvx (congrArg (fun u : C.supp => u.val.val) he)
    have hl := intro21_even_degree_four_child_path_leaf
      G b hG hI hn hb r w hw hlen C a c hac x y l hxa hx hxyv hyvL hya hlx
    exact intro21_even_no_mixed_pendant_arms G b hG hI hn hb
      x.val.val yv k lv hxk hxyv hyvL hlvx.symm hk hyv2 hl
#print axioms Paper7IntroNonattachmentFour.intro21_even_no_nonattachment_degree_four

theorem intro21_even_nonattachment_degree_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : x ≠ a) : G.degree x.val.val ≤ 3 := by
  have hle := (intro21_even_component_degree_four_only_next_to_attachment
    G b hG hI hn hb r w hw hlen C a c hac x hxa).1
  have hne : G.degree x.val.val ≠ 4 := fun hx =>
    intro21_even_no_nonattachment_degree_four G b hG hI hn hb
      r w hw hlen C a c hac x hxa hx
  omega
#print axioms Paper7IntroNonattachmentFour.intro21_even_nonattachment_degree_le_three

end Paper7IntroNonattachmentFour
