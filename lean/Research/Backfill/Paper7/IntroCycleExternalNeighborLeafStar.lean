import Research.Backfill.Paper7.IntroAttachmentLeafStarShape
import Research.Backfill.Paper7.IntroAttachmentZeroOneThree

/-! Each actual neighbor outside the given cycle is transported through
its real deleted-cycle connected component. Full leaf neighborhoods and
canonical 0/1/3 alternatives are conclusions, not graph hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroExternalLeafStar
open SimpleGraph BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroAttachmentLeafStar Paper7IntroZeroOneThree

theorem intro21_even_cycle_external_neighbor_leaf_star
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (c x : V) (hc : c ∈ w.support) (hx : x ∉ w.support) (hxc : G.Adj x c) :
    ∃ Y : Finset V,
      Y = (G.neighborFinset x).erase c ∧ c ∉ Y ∧
      G.neighborFinset x = insert c Y ∧
      (∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = x) ∧
      (∀ y ∈ Y, y ∉ w.support ∧ G.degree y = 1 ∧ y ≠ x ∧ y ≠ c) ∧
      G.degree x = Y.card + 1 ∧
      (Y.card = 0 ∨ Y.card = 1 ∨
        (Y.card = 3 ∧ (G.degree c = 3 ∨ G.degree c = 4))) := by
  let xo : {t : V // t ∉ w.support} := ⟨x, hx⟩
  let Cx := (deleteVertices G {t | t ∈ w.support}).connectedComponentMk xo
  let ax : Cx.supp := ⟨xo, ConnectedComponent.connectedComponentMk_mem⟩
  let cv : {t : V // t ∈ w.support} := ⟨c, hc⟩
  obtain ⟨Y, hY, hdegree, _hne, _hinj, hdata, _hcover, _hNa, hNl⟩ :=
    intro21_even_actual_attachment_leaf_star G b hG hI hn hb r w hw hlen
      Cx ax cv hxc
  change Y = (G.neighborFinset x).erase c at hY
  change G.degree x = Y.card + 1 at hdegree
  have hcases := intro21_even_attachment_zero_one_three G b hG hI hn hb
    r w hw hlen Cx ax cv hxc
  change ((G.neighborFinset x).erase c).card = 0 ∨
    ((G.neighborFinset x).erase c).card = 1 ∨
    (((G.neighborFinset x).erase c).card = 3 ∧
      (G.degree c = 3 ∨ G.degree c = 4)) at hcases
  refine ⟨Y, hY, ?_, ?_, ?_, ?_, hdegree, ?_⟩
  · rw [hY]
    exact Finset.notMem_erase c (G.neighborFinset x)
  · rw [hY]
    exact (Finset.insert_erase ((G.mem_neighborFinset x c).mpr hxc)).symm
  · intro y hy z
    exact hNl ⟨y, hy⟩ z
  · intro y hy
    obtain ⟨⟨t, ht⟩, hd, hyx, hyc⟩ := hdata ⟨y, hy⟩
    have ht' : t.val.val = y := ht
    have hyout : y ∉ w.support := by
      rw [← ht']
      exact t.val.property
    exact ⟨hyout, hd, hyx, hyc⟩
  · simpa only [← hY] using hcases
#print axioms Paper7IntroExternalLeafStar.intro21_even_cycle_external_neighbor_leaf_star

end Paper7IntroExternalLeafStar
