import Research.Backfill.Paper7.IntroOutsideComponentShortArms
import Research.Backfill.Paper7.IntroNonattachmentDegreeFourExclusion

/-! All actual outside-component vertices other than the attachment have
original degree at most two in the original even integral order-21 range.
The Perron-three count is used only in its proved spectral-alternative branch. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroNonattachmentThree
open SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7UnicyclicAttachment Paper7IntroNonattachmentFour
open Paper7IntroEven Paper7IntroFour Paper7IntroCycleNeighborhood

theorem intro21_even_radius_three_nonattachment_short_arms
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (hthree : (integerSpectrum G).count 3 = 1)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val) :
    ∀ x : C.supp, x ≠ a → G.degree x.val.val ≤ 2 ∧
      (2 ≤ G.degree x.val.val → G.Adj x.val.val a.val.val) := by
  obtain ⟨_pair, _hpair, huniq⟩ :=
    unicyclic_component_attachment_endpoints G b hG r w hw hlen C
  have hgate : ∀ (v : {q : V // q ∉ w.support}), v ∈ C.supp →
      ∀ t : {q : V // q ∈ w.support}, G.Adj v.val t.val → v = a.val := by
    intro v hv t hvt
    exact congrArg Prod.fst ((huniq (v, t) ⟨hv, hvt⟩).trans
      (huniq (a.val, c) ⟨a.property, hac⟩).symm)
  have hbound : ∀ x : C.supp, x ≠ a → G.degree x.val.val ≤ 3 :=
    intro21_even_nonattachment_degree_le_three G b hG hI hn hb r w hw hlen C a c hac
  have hfinite : Finite C.supp :=
    Finite.of_injective (fun x : C.supp => x.val.val) (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext hxy))
  let fC : Fintype C.supp := @Fintype.ofFinite C.supp hfinite
  let dC : DecidableEq C.supp := Classical.decEq C.supp
  let eC : DecidableRel C.toSimpleGraph.Adj := fun _ _ => Classical.propDecidable _
  exact @outside_component_short_arms_of_degree_le_three V _ _ G _ hG.1 hI hthree
    {q | q ∈ w.support}
    (Paper7UnicyclicStructure.unicyclic_off_cycle_isAcyclic G b hG r w hw hlen)
    C fC dC eC a hgate hbound
#print axioms Paper7IntroNonattachmentThree.intro21_even_radius_three_nonattachment_short_arms

theorem intro21_even_nonattachment_degree_le_two
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (x : C.supp) (hxa : x ≠ a) : G.degree x.val.val ≤ 2 := by
  rcases intro21_even_actual_spectral_alternatives G b hG hI hn hb with
    hC4 | hC6 | hR3 | hR4
  · obtain ⟨e⟩ : Nonempty (G ≃g cycleGraph 4) := hC4
    exact (cycle_iso_degree_two G 4 (by norm_num) e x.val.val).le
  · obtain ⟨e⟩ : Nonempty (G ≃g cycleGraph 6) := hC6
    exact (cycle_iso_degree_two G 6 (by norm_num) e x.val.val).le
  · obtain ⟨_z, _u, _v, _hz, _hu, _hv, _hn, _hm, _hlimit, hthree, _hfour, _hdev⟩ := hR3
    exact (intro21_even_radius_three_nonattachment_short_arms
      G b hG hI hn hb hthree r w hw hlen C a c hac x hxa).1
  · obtain ⟨_z, _u, _v, _hz, _hu, _hv, _hn, _hm, _hlimit, _hthree, hfour, _hdev⟩ := hR4
    exact (intro21_even_no_top_four G b hG hI hn hb hfour).elim
#print axioms Paper7IntroNonattachmentThree.intro21_even_nonattachment_degree_le_two

end Paper7IntroNonattachmentThree
