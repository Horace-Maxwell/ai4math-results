import Research.Backfill.Paper7.IntroOffCycleComplementPositive
import Research.Backfill.Paper7.IntroStrictHighBranch
import Research.Backfill.Paper7.IntroAttachmentDeletion

/-! Strict spectral and degree bounds for an actual component away from the
intact cycle. Positive complement Ngt is now a conclusion of the graph data. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace Paper7IntroCycleComplement
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroCutGap Paper7IntroHighBranch Paper7IntroHighVertex
open Paper7IntroStrictCut Paper7IntroCycleNeighborhood Paper7UnicyclicAttachment

theorem intro21_even_off_cycle_component_strict_bounds
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (v : V) (hv : v ∉ w.support)
    (C : (vertexDeletedGraph G v).ConnectedComponent)
    (hdisj : ∀ (x : {q : V // q ∈ w.support}) (hx : x.val ≠ v),
      (⟨x.val, hx⟩ : {q : V // q ≠ v}) ∉ C.supp) :
    (∀ t ∈ spec ((vertexDeletedGraph G v).induce C.supp), t < 2) ∧
      (∀ i, ((vertexDeletedGraph G v).induce C.supp).degree i ≤ 3) ∧
      (∀ i : C.supp, G.degree i.val.val ≤ 4) ∧
      (∀ i : C.supp, ¬G.Adj i.val.val v → G.degree i.val.val ≤ 3) := by
  have hp := intro21_even_off_cycle_component_complement_Ngt_pos
    G b hG hI hn hb r w hw hlen v hv C hdisj
  have hN := intro21_even_Ngt_two_le_one G b hG hI hn hb
  have hd := deleted_component_degree_le_three_of_complement_Ngt_positive G hG.1 hN v C hp
  refine ⟨deleted_component_spectrum_lt_two_of_complement_Ngt_positive G hG.1 hN v C hp,
    hd, ?_, ?_⟩
  · intro i
    have hi := hd i
    have hr := deleted_component_original_degree_restore G v C i
    split_ifs at hr <;> omega
  · intro i hiv
    have hi := hd i
    have hr := deleted_component_original_degree_restore G v C i
    rw [ite_eq_right hiv, add_zero] at hr
    omega
#print axioms Paper7IntroCycleComplement.intro21_even_off_cycle_component_strict_bounds

theorem intro21_even_attachment_residual_positive_and_degree_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : {q : V // q ∉ w.support}) (ha : a ∈ C.supp)
    (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val c.val)
    (D : (vertexDeletedGraph G a.val).ConnectedComponent)
    (u : {q : V // q ≠ a.val}) (huD : u ∈ D.supp)
    (huS : u.val ∉ w.support)
    (huC : (⟨u.val, huS⟩ : {q : V // q ∉ w.support}) ∈ C.supp) :
    0 < Ngt ((vertexDeletedGraph G a.val).induce
      (D.suppᶜ : Set {q : V // q ≠ a.val})) 2 ∧
      ∀ i, ((vertexDeletedGraph G a.val).induce D.supp).degree i ≤ 3 := by
  have hgate : ∀ (y : {q : V // q ∉ w.support}), y ∈ C.supp →
      ∀ z : {q : V // q ∈ w.support}, G.Adj y.val z.val → y = a := by
    intro y hy z hyz
    obtain ⟨pair, _hpair, huniq⟩ :=
      unicyclic_component_attachment_endpoints G b hG r w hw hlen C
    have hya := huniq (y, z) ⟨hy, hyz⟩
    have haa := huniq (a, c) ⟨ha, hac⟩
    exact congrArg Prod.fst (hya.trans haa.symm)
  have hdisj := deleted_attachment_component_disjoint_core
    G {q | q ∈ w.support} C a hgate D u huD huS huC
  have hp := intro21_even_off_cycle_component_complement_Ngt_pos
    G b hG hI hn hb r w hw hlen a.val a.property D hdisj
  exact ⟨hp, deleted_component_degree_le_three_of_complement_Ngt_positive
    G hG.1 (intro21_even_Ngt_two_le_one G b hG hI hn hb) a.val D hp⟩
#print axioms Paper7IntroCycleComplement.intro21_even_attachment_residual_positive_and_degree_bound

end Paper7IntroCycleComplement
