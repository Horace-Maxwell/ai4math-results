import Research.Backfill.Paper7.SpectralWindowPass

/-! Source-only partial assembly: exactly conjuncts 3 and 5 of the frozen
pruning contract. This is not the full eleven-conjunct contract. -/
set_option autoImplicit false
namespace Paper7PruningSpectrum
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy

theorem pruning_spectrum_stage :
    (∀ b N : ℕ, 3 ≤ b → b ≤ N → N ≤ 49 → ∀ x, Budget b N x →
      IsIntegralGraph (SG b x.1 x.2) →
      ∃ s, AdmissibleBase b N s ∧
        (∀ i : Fin 8, (s.1 i).val = mult (SG b x.1 x.2) (value i)) ∧
        (Odd b → ∀ i : Fin 8, (s.2 i).val = mult (SG b x.1 x.2) (-(value i : ℝ)))) ∧
    (∀ b N d : ℕ, 3 ≤ b → d ≤ b → N ≤ 49 → ∀ x, Budget b N x →
      IsIntegralGraph (SG b x.1 x.2) → WindowPass true b N d x) :=
  ⟨pruning_actual_spectrum_encoding, pruning_windowPass⟩
#print axioms Paper7PruningSpectrum.pruning_spectrum_stage

end Paper7PruningSpectrum
