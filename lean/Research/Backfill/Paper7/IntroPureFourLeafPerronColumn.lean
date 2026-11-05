import Research.Backfill.Paper7.IntroPureFourLeafSColumn
import Research.Backfill.Paper7.IntroAttachmentLeafStarMomentNorm

/-! One actual normalized graph witness supplies both the local columns
and the positive Perron column. The four/six branch adds no numerical
moment, kernel, coverage, or independent-witness identification premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroFourLeafColumn
open Matrix SimpleGraph BackfillPaper7.Challenge Paper7OddIntegral
open BackfillPaper7.Challenge.Legacy.Algebra
open Paper7IntroFourProjector Paper7IntroZeroOneProjectors Paper7IntroProjectors
open Paper7IntroLeafStarWeights Paper7IntroFour

theorem intro21_even_four_leaf_degree_six_perron_column
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hG : IsUnicyclicWithCycle G b) (hI : IsIntegralGraph G)
    (hn : Fintype.card V ≤ 21) (hb : Even b)
    (r : V) (w : G.Walk r r) (hw : w.IsCycle) (hlen : w.length = b)
    (C : (deleteVertices G {q | q ∈ w.support}).ConnectedComponent)
    (a : C.supp) (c : {q : V // q ∈ w.support}) (hac : G.Adj a.val.val c.val)
    (hm : ((G.neighborFinset a.val.val).erase c.val).card = 4)
    (hd : G.degree c.val = 6) :
    ∃ (Y : Finset V) (i₀ : Y) (eps f : V → ℝ),
      Y = (G.neighborFinset a.val.val).erase c.val ∧ Y.card = 4 ∧
      G.degree a.val.val = Y.card + 1 ∧ a.val.val ≠ c.val ∧
      Function.Injective (fun i : Y => i.val) ∧
      (∀ i : Y, (∃ x : C.supp, x.val.val = i.val) ∧
        G.degree i.val = 1 ∧ i.val ≠ a.val.val ∧ i.val ≠ c.val) ∧
      (∀ x : C.supp, x = a ∨ ∃ i : Y, x.val.val = i.val) ∧
      (∀ z : V, G.Adj a.val.val z ↔ z = c.val ∨ ∃ i : Y, z = i.val) ∧
      (∀ (i : Y) (z : V), G.Adj i.val z ↔ z = a.val.val) ∧
      (∀ v, eps v = 1 ∨ eps v = -1) ∧
      (∀ u v, G.Adj u v → eps u = -eps v) ∧
      (∀ v, 0 < f v) ∧ G.adjMatrix ℝ *ᵥ f = (3 : ℝ) • f ∧
      f i₀.val = 1 ∧ (∀ i : Y, f i.val = 1) ∧
      f a.val.val = 3 ∧ f c.val = 5 ∧ (f ⬝ᵥ f) = 80 ∧
      radiusThreeQ0 (G.adjMatrix ℝ) *ᵥ Pi.single c.val 1 = 0 ∧
      ((G.adjMatrix ℝ) ^ 6) c.val c.val = 456 ∧
      radiusThreeP4 (G.adjMatrix ℝ) *ᵥ Pi.single c.val 1 = 0 ∧
      ((G.adjMatrix ℝ) ^ 4 - (10 : ℝ) • (G.adjMatrix ℝ) ^ 2 + (9 : ℝ) • 1) *ᵥ
        Pi.single c.val 1 = 0 ∧
      radiusThreeS (G.adjMatrix ℝ) *ᵥ Pi.single c.val 1 =
        (45 : ℝ) • (((G.adjMatrix ℝ) ^ 2 - 1) *ᵥ Pi.single c.val 1) ∧
      (∀ v : V, eps v = eps c.val → v ≠ c.val →
        ((G.adjMatrix ℝ) ^ 2) v c.val = f v) := by
  have hleaves : ((G.neighborFinset a.val.val).erase c.val).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨Y, i₀, eps, f, hY, _hmpos, _hm7, _hlt, hda, hne, hinj, hdata,
    hcover, hNa, hNl, _hthree, hs, hflip, hf, hAf, h₀, hweights, ha, hc,
    _hsgn, _hcs, hproj, _hp, _hnrm, _hmom, _hNpos, _hqpos, hnorm⟩ :=
    intro21_even_actual_leaf_star_moment_norm G b hG hI hn hb r w hw hlen C a c hac hleaves
  have hmY : Y.card = 4 := by rw [hY]; exact hm
  have hcY : c.val ∉ Y := by rw [hY]; exact Finset.notMem_erase c.val _
  have hNa' : G.neighborFinset a.val.val = insert c.val Y := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    rw [hNa z]
    constructor
    · rintro (hzc | ⟨i, hzi⟩)
      · exact Or.inl hzc
      · exact Or.inr (hzi.symm ▸ i.property)
    · rintro (hzc | hzY)
      · exact Or.inl hzc
      · exact Or.inr ⟨⟨z, hzY⟩, rfl⟩
  have hNl' : ∀ y ∈ Y, ∀ z, G.Adj y z ↔ z = a.val.val := by
    intro y hy z
    exact hNl ⟨y, hy⟩ z
  have hbound := intro21_even_spectrum_abs_le_three G b hG hI hn hb
  obtain ⟨hQ, hm6, hP, hK, hS⟩ := pure_four_leaf_degree_six_spectral_columns
    G hI hbound a.val.val c.val Y hcY hNa' hNl' i₀.val i₀.property hmY hd
  have hfc : f c.val = 5 := by
    rw [hmY] at hc
    norm_num at hc
    exact hc
  have hN : (f ⬝ᵥ f) = 80 := by
    rw [hmY, hd] at hnorm
    norm_num at hnorm
    exact hnorm
  have hcol : ∀ v : V, eps v = eps c.val → v ≠ c.val →
      ((G.adjMatrix ℝ) ^ 2) v c.val = f v := by
    intro v hv hvc
    have heps : eps v * eps c.val = 1 := by
      rw [hv]
      rcases hs c.val with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    have hsp := (hproj v c.val).1
    rw [hN, hfc, heps] at hsp
    norm_num at hsp
    have hentry := congrFun hS v
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.sub_apply, Matrix.one_apply_ne hvc, sub_zero] at hentry
    linarith only [hsp, hentry]
  exact ⟨Y, i₀, eps, f, hY, hmY, hda, hne, hinj, hdata, hcover, hNa, hNl,
    hs, hflip, hf, hAf, h₀, hweights, ha, hfc, hN, hQ, hm6, hP, hK, hS, hcol⟩
#print axioms Paper7IntroFourLeafColumn.intro21_even_four_leaf_degree_six_perron_column

end Paper7IntroFourLeafColumn
