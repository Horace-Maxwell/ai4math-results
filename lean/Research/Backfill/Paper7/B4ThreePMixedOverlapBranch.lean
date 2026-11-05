import Research.Backfill.Paper7.B4ThreePMixedOverlap
import Research.Backfill.Paper7.ControlB4CertifiedReduction

/-! Source-only dihedral and original-L transport of the three-P overlap
exclusion. In an integral graph, Q must be confined to the missing P site. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem three_p_dihedral_overlap_nonintegral (p q : Fin 4 → ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < p (σ 0)) (hp1 : 0 < p (σ 1))
    (hp2 : 0 < p (σ 2)) (hp3 : p (σ 3) = 0)
    (hq : 0 < q (σ 0)+q (σ 1)+q (σ 2)) : ¬ IsIntegralGraph (SG 4 p q) := by
  intro hG
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p q (p ∘ σ) (q ∘ σ)
    (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  exact three_p_overlap_nonintegral (p ∘ σ) (q ∘ σ) hp0 hp1 hp2 hp3 hq hI
#print axioms Paper7B4Analytic.three_p_dihedral_overlap_nonintegral

theorem three_p_dihedral_integral_q_disjoint (p q : Fin 4 → ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < p (σ 0)) (hp1 : 0 < p (σ 1))
    (hp2 : 0 < p (σ 2)) (hp3 : p (σ 3) = 0)
    (hG : IsIntegralGraph (SG 4 p q)) : q (σ 0) = 0 ∧ q (σ 1) = 0 ∧ q (σ 2) = 0 := by
  have hh : ¬ 0 < q (σ 0)+q (σ 1)+q (σ 2) := by
    intro hq
    exact three_p_dihedral_overlap_nonintegral p q σ hσ hp0 hp1 hp2 hp3 hq hG
  omega
#print axioms Paper7B4Analytic.three_p_dihedral_integral_q_disjoint

theorem original_three_p_overlap_nonintegral (L : Fin 4 → List ℕ)
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : 0 < Paper7Normalize.countP1 4 L (σ 0))
    (hp1 : 0 < Paper7Normalize.countP1 4 L (σ 1))
    (hp2 : 0 < Paper7Normalize.countP1 4 L (σ 2))
    (hp3 : Paper7Normalize.countP1 4 L (σ 3) = 0)
    (hq : 0 < Paper7Normalize.countP2 4 L (σ 0)+Paper7Normalize.countP2 4 L (σ 1)+
      Paper7Normalize.countP2 4 L (σ 2)) : ¬ IsIntegralGraph (sunGraph 4 L) := by
  intro hG
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q := Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  exact three_p_dihedral_overlap_nonintegral p q σ hσ hp0 hp1 hp2 hp3 hq hI
#print axioms Paper7B4Analytic.original_three_p_overlap_nonintegral

end Paper7B4Analytic
