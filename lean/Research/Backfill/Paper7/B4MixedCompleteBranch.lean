import Research.Backfill.Paper7.B4MixedSupportCover
import Research.Backfill.Paper7.B4AdjacentPMixedExclusion
import Research.Backfill.Paper7.B4OppositePCompleteBranch
import Research.Backfill.Paper7.B4ThreePMixedOverlapBranch
import Research.Backfill.Paper7.B4ThreePDisjointExclusion

/-! Source-only complete genuinely mixed forward branch under n<=49.
Every positive P support is derived from the actual parameters. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem mixed_three_support_nonintegral (p q : Fin 4 → ℕ)
    (hcard : (Kp 4 p).card = 3) (hq : 0 < ∑ i, q i) (hn : nOf 4 p q ≤ 49) :
    ¬ IsIntegralGraph (SG 4 p q) := by
  intro hG
  obtain ⟨σ,hσ,hp0,hp1,hp2,hp3⟩ := mixed_three_support_dihedral_case p hcard
  obtain ⟨hq0,hq1,hq2⟩ := three_p_dihedral_integral_q_disjoint p q σ hσ hp0 hp1 hp2 hp3 hG
  have hsum : q (σ 0)+q (σ 1)+q (σ 2)+q (σ 3) = ∑ i, q i := by
    have hh := (Paper7PruningCanonical.dihedral_bijective 4 (by decide) σ hσ).sum_comp q
    simpa only [Fin.sum_univ_four] using hh
  have hq3 : 0 < q (σ 3) := by omega
  exact three_p_dihedral_disjoint_nonintegral p q σ hσ
    hp0 hp1 hp2 hp3 hq0 hq1 hq2 hq3 hn hG
#print axioms Paper7B4Analytic.mixed_three_support_nonintegral

theorem mixed_integral_iso_g20a (p q : Fin 4 → ℕ)
    (hp : 0 < ∑ i, p i) (hq : 0 < ∑ i, q i) (hn : nOf 4 p q ≤ 49)
    (hG : IsIntegralGraph (SG 4 p q)) : Nonempty (SG 4 p q ≃g sunGraph 4 G20a) := by
  rcases integral_genuinely_mixed_p_support p q hp hq hG with htwo | hthree
  · obtain ⟨σ,hσ,hcases⟩ := mixed_two_support_dihedral_cases p htwo
    rcases hcases with ⟨hp0,hp1,hp2,hp3⟩ | ⟨hp0,hp1,hp2,hp3⟩
    · exact False.elim (adjacent_two_p_dihedral_mixed_nonintegral p q σ hσ hp0 hp1 hp2 hp3 hq hG)
    · exact opposite_p_complete_dihedral_iso_g20a p q σ hσ hp0 hp1 hp2 hp3 hq hn hG
  · exact False.elim (mixed_three_support_nonintegral p q hthree hq hn hG)
#print axioms Paper7B4Analytic.mixed_integral_iso_g20a

theorem original_mixed_integral_iso_g20a (L : Fin 4 → List ℕ)
    (hp : 0 < ∑ i, Paper7Normalize.countP1 4 L i)
    (hq : 0 < ∑ i, Paper7Normalize.countP2 4 L i)
    (hn : order 4 L ≤ 49) (hG : IsIntegralGraph (sunGraph 4 L)) :
    Nonempty (sunGraph 4 L ≃g sunGraph 4 G20a) := by
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
  obtain ⟨f⟩ := mixed_integral_iso_g20a p q hp hq hn' hI
  exact ⟨e.trans f⟩
#print axioms Paper7B4Analytic.original_mixed_integral_iso_g20a

end Paper7B4Analytic
