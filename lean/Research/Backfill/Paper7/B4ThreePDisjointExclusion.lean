import Research.Backfill.Paper7.B4ThreePDisjointRank
import Research.Backfill.Paper7.B4ThreePDisjointSimpleSpectrum
import Research.Backfill.Paper7.ControlB4CertifiedReduction

/-! Source-only complete exclusion of the remaining three-P, disjoint-Q
family in the original order bound, with actual graph transport. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem three_disjoint_parameters_nonintegral (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hn : nOf 4 (threePDisjointP a b c) (threePDisjointQ d) ≤ 49) :
    ¬ IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d)) := by
  intro hG
  let p := threePDisjointP a b c
  let q := threePDisjointQ d
  have hcard : (Bplus (SG 4 p q)).card = 4 :=
    three_disjoint_integral_big_card a b c d ha hb hc hd hG
  have hints : ∀ x ∈ Bplus (SG 4 p q), 2 ≤ x ∧ ∃ z : ℤ, x = z := by
    intro x hx
    obtain ⟨hmem,hx2⟩ := Multiset.mem_filter.mp hx
    exact ⟨hx2,Paper7Moments.integral_spec_entry _ hG x hmem⟩
  have hfloor := integral_square_floor_twenty_five (Bplus (SG 4 p q)) hints
  have h2N := three_disjoint_big_count_le_one a b c d hb hd hn hG 2 (by norm_num)
  have h3N := three_disjoint_big_count_le_one a b c d hb hd hn hG 3 (by norm_num)
  have h4N := three_disjoint_big_count_le_one a b c d hb hd hn hG 4 (by norm_num)
  have h2 : ((Bplus (SG 4 p q)).count 2 : ℝ) ≤ 1 := by exact_mod_cast h2N
  have h3 : ((Bplus (SG 4 p q)).count 3 : ℝ) ≤ 1 := by exact_mod_cast h3N
  have h4 : ((Bplus (SG 4 p q)).count 4 : ℝ) ≤ 1 := by exact_mod_cast h4N
  have hS := (Paper7Counting.lemma42_bounds 4 p q (by decide) (by decide) hG).1
  have hnR : (nOf 4 p q : ℝ) ≤ 49 := by exact_mod_cast hn
  change 25*((Bplus (SG 4 p q)).card : ℝ) ≤ S2 (SG 4 p q)+
    21*((Bplus (SG 4 p q)).count 2 : ℝ)+
    16*((Bplus (SG 4 p q)).count 3 : ℝ)+
    9*((Bplus (SG 4 p q)).count 4 : ℝ) at hfloor
  rw [hcard] at hfloor
  norm_num at hfloor
  linarith
#print axioms Paper7B4Analytic.three_disjoint_parameters_nonintegral

theorem three_p_disjoint_nonintegral (p q : Fin 4 → ℕ)
    (hp0 : 0 < p 0) (hp1 : 0 < p 1) (hp2 : 0 < p 2) (hp3 : p 3 = 0)
    (hq0 : q 0 = 0) (hq1 : q 1 = 0) (hq2 : q 2 = 0) (hq3 : 0 < q 3)
    (hn : nOf 4 p q ≤ 49) : ¬ IsIntegralGraph (SG 4 p q) := by
  intro hG
  let a := p 0
  let b := p 1
  let c := p 2
  let d := q 3
  have hpe : p = threePDisjointP a b c := by
    funext i
    fin_cases i <;> simp [a,b,c,threePDisjointP,hp3]
  have hqe : q = threePDisjointQ d := by
    funext i
    fin_cases i <;> simp [d,threePDisjointQ,hq0,hq1,hq2]
  have hn' : nOf 4 (threePDisjointP a b c) (threePDisjointQ d) ≤ 49 := by
    rw [← hpe,← hqe]
    exact hn
  have hG' : IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d)) := by
    rw [← hpe,← hqe]
    exact hG
  exact three_disjoint_parameters_nonintegral a b c d hp0 hp1 hp2 hq3 hn' hG'
#print axioms Paper7B4Analytic.three_p_disjoint_nonintegral

theorem three_p_dihedral_disjoint_nonintegral (p q : Fin 4 → ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < p (σ 0)) (hp1 : 0 < p (σ 1))
    (hp2 : 0 < p (σ 2)) (hp3 : p (σ 3) = 0)
    (hq0 : q (σ 0) = 0) (hq1 : q (σ 1) = 0)
    (hq2 : q (σ 2) = 0) (hq3 : 0 < q (σ 3))
    (hn : nOf 4 p q ≤ 49) : ¬ IsIntegralGraph (SG 4 p q) := by
  intro hG
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p q (p ∘ σ) (q ∘ σ)
    (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hbij := Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ
  have hP : ∑ i, (p ∘ σ) i = ∑ i, p i := hbij.sum_comp p
  have hQ : ∑ i, (q ∘ σ) i = ∑ i, q i := hbij.sum_comp q
  have hn' : nOf 4 (p ∘ σ) (q ∘ σ) ≤ 49 := by
    simpa only [nOf,hP,hQ] using hn
  exact three_p_disjoint_nonintegral (p ∘ σ) (q ∘ σ)
    hp0 hp1 hp2 hp3 hq0 hq1 hq2 hq3 hn' hI
#print axioms Paper7B4Analytic.three_p_dihedral_disjoint_nonintegral

theorem original_three_p_disjoint_nonintegral (L : Fin 4 → List ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < Paper7Normalize.countP1 4 L (σ 0))
    (hp1 : 0 < Paper7Normalize.countP1 4 L (σ 1))
    (hp2 : 0 < Paper7Normalize.countP1 4 L (σ 2))
    (hp3 : Paper7Normalize.countP1 4 L (σ 3) = 0)
    (hq0 : Paper7Normalize.countP2 4 L (σ 0) = 0)
    (hq1 : Paper7Normalize.countP2 4 L (σ 1) = 0)
    (hq2 : Paper7Normalize.countP2 4 L (σ 2) = 0)
    (hq3 : 0 < Paper7Normalize.countP2 4 L (σ 3))
    (hn : order 4 L ≤ 49) : ¬ IsIntegralGraph (sunGraph 4 L) := by
  intro hG
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q := Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hc := Fintype.card_congr e.toEquiv
  change order 4 L = order 4 (pq 4 p q) at hc
  rw [Paper7Setup.sg_order] at hc
  have hn' : nOf 4 p q ≤ 49 := by omega
  exact three_p_dihedral_disjoint_nonintegral p q σ hσ
    hp0 hp1 hp2 hp3 hq0 hq1 hq2 hq3 hn' hI
#print axioms Paper7B4Analytic.original_three_p_disjoint_nonintegral

end Paper7B4Analytic
