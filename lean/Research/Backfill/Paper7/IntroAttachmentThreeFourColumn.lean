import Research.Backfill.Paper7.IntroThreeLeafColumnSaturation
import Research.Backfill.Paper7.IntroAttachmentLeafStarMomentNorm
import Research.Backfill.Paper7.IntroPureLeafStarCycleFourthConstraint

/-! The original m=3,d=4 branch produces its saturated column on the
same actual Perron witness. No norm, matrix moment, column or integer-value
assumption is added to the original graph hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroThreeFourColumn
open SimpleGraph Matrix BackfillPaper7.Challenge
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroLeafStarWeights Paper7IntroPureLeafConstraints Paper7IntroFour
open Paper7IntroThreeLeafSaturation

theorem intro21_even_three_leaf_degree_four_perron_column
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 3)
    (hd : G.degree c.val = 4) :
    ∃ (Y : Finset V) (i₀ : Y) (eps f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧ Y.card = 3 ∧
      c.val ∉ Y ∧ G.neighborFinset a.val.val = insert c.val Y ∧
      (∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a.val.val) ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ v, eps v = 1 ∨ eps v = -1) ∧
      (∀ u v, G.Adj u v → eps u = -eps v) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f i₀.val = 1 ∧ (∀ y ∈ Y, f y = 1) ∧ f a.val.val = 3 ∧ f c.val = 6 ∧
      (f ⬝ᵥ f) = 240 ∧
      (∑ v, if eps v = eps c.val then f v ^ 2 else 0) = 120 ∧
      ((G.adjMatrix ℝ) ^ 4) c.val c.val = 28 ∧
      (∀ t, eps t = eps c.val → t ≠ c.val → t ∉ Y →
        f t = 3 * ((G.adjMatrix ℝ) ^ 2) t c.val) := by
  have hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty :=
    Finset.card_pos.mp (by rw [hm]; norm_num)
  obtain ⟨Y, i₀, eps, f, hY, _hmpos, _hmseven, _hmnine, _hda, _hne,
      _hinj, hdata, hcover, _hNa, hNl, _hthree, hs, hflip, hf, hAf,
      hbase, hleaf, ha, hc, _hsignY, _hsignc, _hproj, hplus, hminus,
      _hmom, _hNpos, _hqpos, hN⟩ :=
    intro21_even_actual_leaf_star_moment_norm
      G b hG hI hn hb r w hw hlen C a c hac hleaves
  have hY3 : Y.card = 3 := by rw [hY]; exact hm
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hNa' : G.neighborFinset a.val.val = insert c.val Y := by
    rw [hY]
    exact (Finset.insert_erase ((G.mem_neighborFinset a.val.val c.val).mpr hac)).symm
  have hNl' : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a.val.val := by
    intro y hy z
    exact hNl ⟨y, hy⟩ z
  have hleaf' : ∀ y ∈ Y, f y = 1 := by
    intro y hy
    exact hleaf ⟨y, hy⟩
  have hfc : f c.val = 6 := by norm_num [hY3] at hc; exact hc
  have hN240 : f ⬝ᵥ f = 240 := by norm_num [hY3, hd] at hN; exact hN
  have hside : (∑ v, if eps v = eps c.val then f v ^ 2 else 0) = 120 := by
    rcases hs c.val with hsc | hsc
    · rw [hsc]
      norm_num [hN240] at hplus
      exact hplus
    · rw [hsc]
      norm_num [hN240] at hminus
      exact hminus
  have hbound := intro21_even_spectrum_abs_le_three G b hG hI hn hb
  have hM4 := pure_leaf_star_cycle_fourth_constraint
    G hI hbound a.val.val c.val Y hcY hNa' hNl' i₀.val i₀.property
  have hM28 : ((G.adjMatrix ℝ) ^ 4) c.val c.val = 28 := by
    norm_num [hY3, hd] at hM4
    exact hM4
  have hcol := actual_three_leaf_four_column_saturation
    G eps f hflip hAf a.val.val c.val Y hcY hY3 hNa' hNl' hleaf' hfc hd hside hM28
  exact ⟨Y, i₀, eps, f, hY, hY3, hcY, hNa', hNl', hdata, hcover, hs, hflip,
    hf, hAf, hbase, hleaf', ha, hfc, hN240, hside, hM28, hcol⟩
#print axioms Paper7IntroThreeFourColumn.intro21_even_three_leaf_degree_four_perron_column

end Paper7IntroThreeFourColumn
