import Research.Backfill.Paper7.B4MixedOppositeClassification
import Research.Backfill.Paper7.ControlB4CertifiedReduction

/-! Source-only dihedral and original-arm-list transport for the complete
mixed opposite G20a branch. No order bound is needed for this subbranch. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Matrix Classical

theorem mixed_opposite_dihedral_integral_iso_g20a (p q : Fin 4 → ℕ)
    (hG : IsIntegralGraph (SG 4 p q))
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : (p ∘ σ) 0 = 0) (hp1 : (p ∘ σ) 1 = 1)
    (hp2 : (p ∘ σ) 2 = 0) (hp3 : (p ∘ σ) 3 = 1)
    (hq1 : (q ∘ σ) 1 = 0) (hq3 : (q ∘ σ) 3 = 0) :
    Nonempty (SG 4 p q ≃g sunGraph 4 G20a) := by
  obtain ⟨e⟩ := Paper7Setup.sg_iso_of_dihedral 4 p q
    (p ∘ σ) (q ∘ σ) (by decide) σ hσ rfl rfl
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  obtain ⟨f⟩ := mixed_opposite_integral_iso_g20a (p ∘ σ) (q ∘ σ)
    hp0 hp1 hp2 hp3 hq1 hq3 hI
  exact ⟨e.trans f⟩
#print axioms Paper7B4Analytic.mixed_opposite_dihedral_integral_iso_g20a

theorem original_mixed_opposite_branch (L : Fin 4 → List ℕ)
    (hG : IsIntegralGraph (sunGraph 4 L))
    (σ : Fin 4 → Fin 4) (hσ : IsDihedral 4 σ)
    (hp0 : (Paper7Normalize.countP1 4 L ∘ σ) 0 = 0)
    (hp1 : (Paper7Normalize.countP1 4 L ∘ σ) 1 = 1)
    (hp2 : (Paper7Normalize.countP1 4 L ∘ σ) 2 = 0)
    (hp3 : (Paper7Normalize.countP1 4 L ∘ σ) 3 = 1)
    (hq1 : (Paper7Normalize.countP2 4 L ∘ σ) 1 = 0)
    (hq3 : (Paper7Normalize.countP2 4 L ∘ σ) 3 = 0) :
    Nonempty (sunGraph 4 L ≃g sunGraph 4 G20a) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q :=
    Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  obtain ⟨f⟩ := mixed_opposite_dihedral_integral_iso_g20a p q hI σ hσ
    hp0 hp1 hp2 hp3 hq1 hq3
  exact ⟨e.trans f⟩
#print axioms Paper7B4Analytic.original_mixed_opposite_branch

end Paper7B4Analytic
