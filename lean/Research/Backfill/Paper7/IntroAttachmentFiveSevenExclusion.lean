import Research.Backfill.Paper7.IntroPerronHalfNormSaturation
import Research.Backfill.Paper7.IntroAttachmentLeafStarMomentNorm

/-! Exclude the canonical (five leaves,parent degree seven) and
(seven leaves,parent degree five) branches from the original graph.
All normalized data come from one actual leaf-star/Perron witness. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroHalfNorm
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroLeafStarWeights

theorem intro21_even_attachment_not_five_seven_or_seven_five
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (walk : G.Walk r r) (hw : walk.IsCycle) (hlen : walk.length = b)
    (C : (deleteVertices G {q | q ∈ walk.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ walk.support}) (hac : G.Adj a.val.val c.val) :
    ¬ (((G.neighborFinset a.val.val).erase c.val).card = 5 ∧ G.degree c.val = 7) ∧
      ¬ (((G.neighborFinset a.val.val).erase c.val).card = 7 ∧ G.degree c.val = 5) := by
  have hnot : ¬ ((((G.neighborFinset a.val.val).erase c.val).card = 5 ∧ G.degree c.val = 7) ∨
      (((G.neighborFinset a.val.val).erase c.val).card = 7 ∧ G.degree c.val = 5)) := by
    intro hcase
    have hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty := by
      apply Finset.card_pos.mp
      rcases hcase with h | h <;> omega
    obtain ⟨Y, _i₀, eps, f, hY, _hmpos, _hmseven, _hmnine, _hda, _hne,
      _hinj, _hdata, _hcover, _hNa, _hNl, _hthree, hs, hflip, hf, hAf,
      _hbase, _hleaf, ha, hc, _hsignY, _hsignc, _hproj, hplus, hminus,
      _hmom, _hNpos, _hqpos, hN⟩ :=
      intro21_even_actual_leaf_star_moment_norm
        G b hG hI hn hb r walk hw hlen C a c hac hleaves
    have hycase : (Y.card = 5 ∧ G.degree c.val = 7) ∨
        (Y.card = 7 ∧ G.degree c.val = 5) := by
      simpa only [hY] using hcase
    rcases hycase with ⟨hm, hd⟩ | ⟨hm, hd⟩
    · have hfc : f c.val = 4 := by norm_num [hm] at hc; exact hc
      have hN45 : f ⬝ᵥ f = 45 := by norm_num [hm, hd] at hN; exact hN
      apply perron_half_norm_cycle_contradiction G a.val.val c.val hac.symm
        eps f hs hflip hf hAf hplus hminus (3 / 2 : ℝ) ?_ ?_ ?_
        walk hw c.property a.val.property
      · norm_num [hfc, ha, hd]
      · norm_num [hN45, ha, hd]
      · norm_num [hfc]
    · have hfc : f c.val = 2 := by norm_num [hm] at hc; exact hc
      have hNhalf : f ⬝ᵥ f = 45 / 2 := by norm_num [hm, hd] at hN; exact hN
      apply perron_half_norm_cycle_contradiction G a.val.val c.val hac.symm
        eps f hs hflip hf hAf hplus hminus (3 / 4 : ℝ) ?_ ?_ ?_
        walk hw c.property a.val.property
      · norm_num [hfc, ha, hd]
      · norm_num [hNhalf, ha, hd]
      · norm_num [hfc]
  exact ⟨fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
#print axioms Paper7IntroHalfNorm.intro21_even_attachment_not_five_seven_or_seven_five

end Paper7IntroHalfNorm
