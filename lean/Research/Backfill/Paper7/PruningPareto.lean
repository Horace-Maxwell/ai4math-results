import Research.Backfill.Paper7.LegacyEnumeration

/-! Uncompiled Root candidate for the finite Pareto part of the frozen
enumeration contract. This file proves no complete main contract by itself. -/

set_option autoImplicit false
noncomputable section

namespace Paper7Pruning
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem featureDominates_refl (b : ℕ) (s : SpectralCounts) :
    FeatureDominates b s s := by
  exact ⟨le_rfl, le_rfl, fun _ _ _ => ⟨le_rfl, le_rfl⟩⟩
#print axioms Paper7Pruning.featureDominates_refl

theorem featureDominates_trans (b : ℕ) {s t u : SpectralCounts}
    (hst : FeatureDominates b s t) (htu : FeatureDominates b t u) :
    FeatureDominates b s u := by
  refine ⟨hst.1.trans htu.1, hst.2.1.trans htu.2.1, ?_⟩
  intro m hm1 hm9
  exact ⟨(hst.2.2 m hm1 hm9).1.trans (htu.2.2 m hm1 hm9).1,
    (hst.2.2 m hm1 hm9).2.trans (htu.2.2 m hm1 hm9).2⟩
#print axioms Paper7Pruning.featureDominates_trans

theorem admissible_has_pareto_maximal (cyc : Bool) (b N : ℕ)
    (s : SpectralCounts) (hs : Admissible cyc b N s) :
    ∃ t, ParetoMaximal cyc b N t ∧ FeatureDominates b s t := by
  classical
  let ord : Preorder SpectralCounts := {
    le := FeatureDominates b
    lt := fun a c => FeatureDominates b a c ∧ ¬ FeatureDominates b c a
    le_refl := featureDominates_refl b
    le_trans := fun _ _ _ => featureDominates_trans b
    lt_iff_le_not_ge := fun _ _ => Iff.rfl }
  obtain ⟨t, hst, ht, hmax⟩ :=
    @Finite.exists_le_maximal SpectralCounts ord inferInstance
      (Admissible cyc b N) s hs
  refine ⟨t, ⟨ht, ?_⟩, hst⟩
  intro u hu htu
  exact hmax hu htu
#print axioms Paper7Pruning.admissible_has_pareto_maximal

end Paper7Pruning
